# Prefix–collar decoupling, confinement, and critical thresholds

- **ID:** critical-ratio-window-confinement-and-threshold-law
- **Stage:** 1-in-progress
- **Status:** Decoupling and collar Gårding formalized; primitive threshold equality formalized; whole-space polar transfer open.
- **Target:** \(R_c=R_c^{\mathrm{nn}}=R_c^{\mathrm{polar}}\), \(R_c^\perp=\inf_{A\ge0}R_1(A)\), and exponential onset lower bounds.

## Definitions

Fix \(\varphi=\mathrm{tiltedUnitSpline}\), \(L=\log N\), \(c_N\ge1\), and
\(c_N^8/L\to R>0\). Put \(Q=\lfloor L^{13/32}\rfloor\),
\(X=\lfloor\exp(\sqrt L)\rfloor\),
\(\theta=(1+\log L)^{-5}\), \(Y=\lfloor N^\theta\rfloor\), and
\(M=N/\mathrm{linearDefectCutoff}(c_N)\).
Write \(x=\sum_{m\le Q}b_mv_m+u_0+u_1+w\), with the three complement bands
ending at \(X,Y,N\). Let \(U\) be the normalized atomic profile of the collar of \(w\).

## Formalized statements

1. **Sharp physical-tearing obstruction.** The least-prime quasimode above \(Q\) has
   prefix–collar Schur ratio tending to \(4/13\). Keeping conductors through \(Y\)
   whole restores arbitrarily small prefix–collar Schur payment.
   Lean: `PrefixCollarSchurObstructionAndFarDecoupling`,
   `FiniteConductorCollarReductionAndPolarDecoupling`.

2. **Collar restriction is essential.** Unrestricted atomic Gårding fails; collar Gårding holds.
   Nonpositive discrete directions cannot vanish on a terminal logarithmic window.
   Lean: `UnrestrictedAtomicGardingFailsAndCollarGardingHolds`,
   `NegativeDirectionsCannotEscapeLogarithmicWindows`.

3. **Nonpolar cancellation.** For every fixed \(m\ge2\),
   \((L/c_N^2)D_7(r_m)\to0\). The growing nonpolar packet has
   \((c_N^7/L)\sum_{2\le m\le Q}D_7(r_m)/E_m\to0\), uniformly on positive compact
   critical bands. Deep residuals and all non-collar pairings are absorbed by the three-band reserves.
   Lean: `NonpolarCollarResidualsVanish`, `AllRatioDeepConductorPairings`,
   `LowConductorCollarPairingsAndWindowLocalizedGarding`.

4. **Whole-space Gårding.** The packet diagonal, complement norm, prefix, seventh-mass,
   eighth-mass, and Lévy reserves are bounded by the complete energy plus terminal-window mass
   and the sole scalar loss \(C c_N b_1^2/L\). The window length satisfies
   \(A\le\tfrac14\log(R+1)+C_{\mathrm{len}}\).
   On the primitive hyperplane the scalar loss is absorbed; the same far component has an
   arbitrarily accurate energy bridge.
   Lean: `WholeSpaceCollarGarding`, `PrimitiveDirectionsHaveCompactCollarProfiles`.

5. **Existing threshold bounds.**
   \[
   0<R_c\le R_c^{\mathrm{nn}}\le R_c^{\mathrm{polar}}
     \le R_c^\perp=R_c^{\mathrm{high}}
     =\inf_{A\ge0}R_1(A).
   \]
   The window infimum is at least \(c_0e^{6a}\), and the polar threshold at least
   \(c_1e^{c_2a}\), for \(0\le a\le a^*(\zeta)\).
   Each threshold being infinite is equivalent to \(a^*(\zeta)=\infty\) and RH.
   Lean: `TheCriticalPositivityThresholdLaw`, `PolarPaymentThresholdHierarchy`,
   `PolarPaymentThresholdGrowsExponentially`.

Axiom audits for these results use only `propext, Classical.choice, Quot.sound`.

## Proof mechanism for the primitive equality

Split each fixed nonpolar residual at \(\lfloor\delta N\rfloor\). The lower dual-seventh
mass is \(O_m(\delta)\); periodic cancellation makes the upper mass vanish. A finite-conductor
tail estimate sums over the growing packet. Three-band Schur payment and the primitive coordinate
bound absorb the remaining polar coefficient square. Any primitive nonpositive sequence therefore
has unit-normalized collar profiles with bounded eighth exponential mass and asymptotically
nonpositive Weil form. Strong compactness and the critical alias lower bound contradict
\(R<\inf_A R_1(A)\).

Lean: `PrimitiveCriticalThresholdEqualsWindowThreshold`; final file check and four axiom audits pass, including the sixth-exponential and logarithmic consequences.

## Remaining whole-space obligation

Prove sampled Lipschitz approximation of the conductor-one row on each fixed terminal fraction,
then transfer its known smooth-window source limit to arbitrary strong collar-profile limits.
The logarithmic endpoint singularity and finite Mangoldt jumps require explicit square-mean
control. This is tracked in
[cact-whole-space-threshold-onset.md](cact-whole-space-threshold-onset.md).

With that transfer, normalize a bad sequence by \(\|U\|_2^2+\beta^2=1\),
\(\beta=b_1/\sqrt L\), retain the actual scalar pole energy, and use polar payment at a
strictly larger ratio. Its strict window-and-pole reserve gives the contradiction.
The resulting exponent is the proved polar-payment constant \(c_2>0\); no specific
\(1/4\) exponent is asserted.

## Completion criteria

- Primitive threshold equality and its sixth-exponential/logarithmic consequences are verified.
- Prove and audit polar row transfer and whole-space threshold equality.
- Wire finished modules; promote this card only after all stated targets pass Lean.

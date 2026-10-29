# RH research frontier

The research has several distinct source-level frontiers: positivity of complete overlapping Weil forms; positivity of signed theta derivatives at unbounded order; an exact theta-clock history budget; lower bounds for completed Suzuki and CCM currents; arithmetic index bounds; cumulative divisor covariance; and signed prime-pair estimates.

Substantial unconditional statements sit immediately beside RH-equivalent conditions. The distinction is in the quantifiers and the retained source terms. Fixed overlap, fixed conductor, fixed matrix order, an existential height certificate, and a cofinal estimate are different mathematical achievements. An equivalence at the RH endpoint does not transfer an estimate between them.

**Complete atomic Weil positivity: an explicit range and a sharp limitation of its certificate.**

For the plateau profile $\varphi_0=\mathrm{plateau}(1/1000)$, with width $w=c/N$, the complete Weil matrix is eventually positive definite for every fixed
$$
0<c<1+\delta_*,
\qquad
\delta_*=\frac1{107520002048050000}.
$$
For $c=1+\delta$, $0\le\delta\le\delta_*$, its asymptotic lower bound is
$$
F(\delta)=\frac1{25}
-2000\delta\left[1+1024000\left(2100000+\frac1{25}\right)\right]:
$$
for every $\varepsilon>0$, one sufficiently large horizon gives
$$
\langle W_{N,c}x,x\rangle\ge(F(\delta)-\varepsilon)\|x\|^2
\quad\text{for every }x.
$$
Strict positivity uses $\delta<\delta_*$. The endpoint is a boundary of this certificate, not a demonstrated spectral transition.

The scalar optimization behind this bound is itself sharp. Under the three inputs
$$
E\ge1/25,\qquad E\ge-2100000+D/1024000,\qquad
|F-E|\le e(D+1),\quad D\ge0,
$$
the lower envelope $1/25-e[1+1024000(2100000+1/25)]$ is attained. Reoptimizing these same inputs cannot produce a macroscopic overlap theorem. Such a theorem needs additional structure.

Lean anchors: `eventually_completeWeilMatrix_posDef_certified`, `eventually_completeWeilMatrix_certified_floor`, and `reference_coercivity_floor_attained` in [OptimizedTransMetzlerFloor](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/OptimizedTransMetzlerFloor.lean); the full fixed-$c$ range in [CompleteWeilLengthHeight](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/CompleteWeilLengthHeight.lean).

Two further boundaries matter.

- The complete form is positive in part of the range where a unimodular Metzler gauge does not exist. The Liouville weight $\lambda\Lambda$ has an eventual negative atomic test for every fixed $c\ge1/2$. Thus this positivity theorem detects arithmetic information beyond the gauge mechanism. See [ExplicitPlateauParameters](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/ExplicitPlateauParameters.lean) and `eventually_liouville_weilQuadTw_neg_transMetzlerProfile` in [LiouvilleTwinSelectivity](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/LiouvilleTwinSelectivity.lean).
- For the Steklov profile, RH is equivalent to eventual positivity for **all coefficient vectors** along
  $$
  c_N=(\log\log N)(\log\log\log N)^\beta,\qquad\beta>2.
  $$
  This is `riemannHypothesis_iff_steklovDCProfile_nonneg_superGevrey` in [SuperGevreyCriticalGrowth](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/SuperGevreyCriticalGrowth.lean). The plateau and Steklov profiles differ. Separate eventual theorems for every fixed $c$ do not give the required horizon along $c_N$.

The concrete overlap target is a complete-form estimate at macroscopic $c$, with a quantified horizon and a profile compatible with exhaustion. A theorem at $c=3/2$, for example, would be substantial but would not itself supply the growing-overlap theorem.

**Critical arithmetic correlations: full Grams, exact radicals, and moving affine parameters.**

The arithmetic input extends beyond a scalar curvature floor. For
$$
S_k(\zeta)=\sum_{r<k}\zeta^r,\qquad
G_m(i,j)=\operatorname{Re}\sum_{\zeta\ {\rm primitive}\ m}
S_i(\zeta)\overline{S_j(\zeta)},
$$
the exact quadratic identity is
$$
\sum_{i,j}a_i a_jG_m(k_i,k_j)
=\sum_{\zeta\ {\rm primitive}\ m}\left|\sum_i a_iS_{k_i}(\zeta)\right|^2.
$$
Its radical is classified: for $m>0$, vanishing is equivalent to divisibility of
$$
\sum_i a_i\sum_{r<k_i}X^r
$$
by $\Phi_m$. For a family of conductors, the condition holds at every conductor in that family. This identifies the null directions that any coercivity argument must handle.

There is also an exact cross-conductor completion:
$$
\sum_{\substack{m\mid Q\\m\ne1}}G_m(i,j)
=Q\min(i,j)-ij,\qquad 0\le i,j\le Q.
$$
Thus a full divisor family recovers the discrete bridge kernel, including its off-diagonal entries. These are `primitivePrefixGram_quadratic_eq`, `primitivePrefixGram_quadratic_eq_zero_iff_cyclotomic_dvd`, and `sum_nontrivial_divisors_primitivePrefixGram` in [the Gram completion](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheArithmeticCurvatureHasAnExactGramCompletion.lean), [the radical classification](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/CyclotomicDivisibilityClassifiesTheOverlapGramRadical.lean), and [the divisor bridge](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/AllDivisorConductorsRecoverTheDiscreteBridge.lean).

The conductor-uniform scalar floor remains useful:
$$
\frac{A_m(t)}{\varphi(m)}
\ge\{t\}(1-\{t\}),\qquad m>1,\ t\ge0.
$$
Here
$$
A_m(k+u)=(1-u)G_m(k,k)+uG_m(k+1,k+1),\qquad 0\le u<1.
$$

The curvature floor uses the norm of a nonzero cyclotomic integer. See `fract_quadratic_le_normalized_arithmeticOverlapCurvature` in [CyclotomicNormGivesAConductorUniformCurvatureFloor](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/CyclotomicNormGivesAConductorUniformCurvatureFloor.lean). The full Gram and its radical give more information than this diagonal inequality.

Prime averaging also has substantial uniformity. For fixed $q>0$ and fixed natural endpoints $0<A\le B$,
$$
\sum_{AN<k\le BN}\frac{\Lambda(k)}k\,c_q(kn+h)
\longrightarrow
(\log B-\log A)\frac{c_q(n)c_q(h)}{\varphi(q)}
$$
**uniformly over all $n,h\in\mathbb N$**. Both may move with $N$. Moreover, one horizon controls every finite complex Gram packet on $\mathbb Z/q\mathbb Z$, with discrepancy bounded by
$$
\varepsilon\sum_{r\bmod q}
\left|\sum_i x_i v_i(r)\right|^2.
$$
The coefficient vectors, packet size, and cross terms are included. The fixed parameter is the residue modulus.

Lean anchors: `eventually_affineRamanujanPrimeWindow_uniform` in [ActualAffinePrimeWindowsAreUniformInTheirParameters](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/ActualAffinePrimeWindowsAreUniformInTheirParameters.lean) and `eventually_primeWindow_all_complex_Gram_packets` in [PrimeResidueWindowsControlEveryGramPacket](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/PrimeResidueWindowsControlEveryGramPacket.lean).

For a fixed $C^2$ profile $\varphi$ supported on $[0,1]$, with $M=\int\varphi^2>0$, every
$$
b<\frac{\mathrm{bumpRobin}(\varphi,1)}M
+\mathrm{completeWeilPoleShift}(\varphi,1)-\log(2\pi)
$$
is eventually a lower bound for every eigenvalue, simultaneously over all $0<c\le1$. For every fixed energy cap and every squared-norm tolerance $\eta>0$, one finite Ramanujan family approximates every unit vector below that cap within $\eta$, uniformly throughout this range. See [OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching.lean) and [OneRamanujanFamilyDetectsAllBoundedEnergiesThroughTouching](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/OneRamanujanFamilyDetectsAllBoundedEnergiesThroughTouching.lean).

The remaining operator problem has precise constraints:

- **Conductor growth and source identification.** Fixed-modulus packet uniformity must be connected to the actual logarithmic successor-shell weights, with control as the required conductor family grows.
- **Transport between annuli.** Ramanujan packets have two-sided frame bounds $1/4$ and $5/4$ on $(A,2A]$ when $A\ge4Q(Q-1)$. The literal prime kernel within that annulus is zero. Its nontrivial action connects different annuli. See [AnnularRamanujanFamiliesHaveTwoSidedFrames](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/AnnularRamanujanFamiliesHaveTwoSidedFrames.lean).
- **A divergent positive row contribution.** The normalized plateau successor fiber grows like a positive constant times $\log N$ for every $c>1$. Hence a horizon-independent absolute row bound cannot justify the comparison. The divergence does not disprove positivity of the completed form. See `tendsto_plateauSuccessorFiber_div_log` and `plateauSuccessorFiber_atTop` in [FixedOverlapHasLogarithmicDivisorRows](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/FixedOverlapHasLogarithmicDivisorRows.lean).
- **Exact finite shells.** The upper shell condition is $r<a(e^w-1)$, from $|\log(a+r)-\log a|<w$, not its linearized approximation. See [ExactSuccessorShellWindows](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/ExactSuccessorShellWindows.lean).
- **Complement cost.** A positive compression must be accompanied by control of the remaining blocks. Eliminating a positive block $D$ leaves $A-BD^{-1}B^*$. The cyclotomic Gram alone does not estimate this subtraction.

There is concrete finite-flip trial mathematics as well. The $p=11$ packet on conductors $1,11,121$ has coefficient square mass one and an exact untwisted Weil-energy limit at $c=99/100$. A proposed upper-margin expression is strictly negative. These are separate statements: the untwisted limit and the scalar margin do not themselves identify that margin with the complete flipped form. The missing theorem is that source comparison. See [ElevenPacket](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/BoundedOverlap/ElevenPacket.lean) and [ElevenTrialMargin](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/BoundedOverlap/ElevenTrialMargin.lean).

**Theta source positivity: global three-node matrices and a strict rank-seven signed hierarchy.**

Let $k_a$ be the actual center-mixed theta density, $0<a<1/2$. Every three-node matrix
$$
[k_a(x_i-x_j)]_{i,j<3}
$$
is positive semidefinite, for arbitrary real nodes. The source proof passes through global reflected correlation-angle subadditivity and positive center integration. The even block of the equispaced four-node matrix is also positive semidefinite for every spacing. This does not assert positivity of its odd block or of arbitrary four-node packets.

Lean anchors: `thetaCuspCenterMixedGramThree_posSemidef` in [ThetaCuspCenterMixedThreePositiveOrientationLaw](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspCenterMixedThreePositiveOrientationLaw.lean), the source theorem in [HedenmalmCenterMixedCorrelationAngle](../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmCenterMixedCorrelationAngle.lean), and `thetaCuspCenterMixedFourPlusBlock_posSemidef` in [ThetaCuspCenterMixedFourPointEvenGlobal](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspCenterMixedFourPointEvenGlobal.lean).

A second, distinct hierarchy uses signed derivatives:
$$
s_a(2n)=(-1)^n k_a^{(2n)}(0),\qquad s_a(2n+1)=0,\qquad
H_{a,N}=[s_a(i+j)]_{i,j<N}.
$$
The **full $H_{a,7}$ is positive definite for every $0<a<1/2$**. The complete hierarchy satisfies
$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\forall\,0<a<1/2,\quad s_a\text{ belongs to the complete Hankel cone}.
$$
The Fourier normalization and moment identification are part of this source theorem. Positivity of ordinary moments of a positive theta density is a different assertion; the alternating derivative signs above are essential.

Lean anchors: `thetaCuspCenterMixedSignedHankel_seven_posDef` in [ThetaCuspCenterMixedSeventhRankStrict](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspCenterMixedSeventhRankStrict.lean) and `thetaCuspCenterMixedSignedJetCone_iff_riemannHypothesis` in [ThetaCuspCenterMixedSignedJetCompleteness](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspCenterMixedSignedJetCompleteness.lean).

Strictness also has a spatial consequence: for each admissible $a$, one radius $\delta(a)>0$ makes **every six distinct nodes of diameter below $\delta(a)$** a positive-definite packet, with no restriction on their relative gaps. See `exists_thetaCuspCenterMixedGramSix_posDef_cluster` in [ThetaCuspCenterMixedSixPointCluster](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspCenterMixedSixPointCluster.lean).

The successor condition is an exact source integral. Whenever $H_{a,n}>0$,
$$
H_{a,n+1}\succeq0
\Longleftrightarrow
\int_0^\infty r\sinh(ar)\,
\mathrm{thetaCuspNativeSuccessorSource}(a,n,r/2)\,dr\ge0.
$$
See `thetaCuspCenterMixedSignedHankel_succ_posSemidef_iff_nativeIntegral_nonneg` in [ThetaCuspCenterMixedSuccessorSource](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspCenterMixedSuccessorSource.lean). Rank-seven strictness supplies its head premise for the next section. An all-order bound must control these native integrals and preserve the strictness required for further successor steps; the fixed-rank theorems do not supply that induction.

**The actual theta clock: an exact first-zero budget with a bounded obstruction set.**

For the actual Borel derivative kernel $K=B'$, let $P$ be the primitive of the clock response and
$$
D(t)=\int_0^t\frac{P(s)}s\,ds.
$$
The exact Volterra equation has coefficient one:
$$
P+P*K=tK.
$$
Its history equation is
$$
tD'(t)=tK(t)+
\int_0^t D(s)\,[K(t-s)-sK'(t-s)]\,ds.
$$
These are source identities, with all quantities attached to the actual theta clock. See [LiEvenCrossActualClockPrimitiveVolterra](../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockPrimitiveVolterra.lean) and [LiEvenCrossActualClockHistoryBarrier](../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockHistoryBarrier.lean).

Write $H_t(s)=K(t-s)-sK'(t-s)$, and use the source cutoff $\ell(t)=K(t)/(4K'(t))$. The exact budget decomposition is
$$
\begin{aligned}
C_{\rm out}(t)&=\int_{\ell(t)}^t D(s)(-H_t(s))\,ds,\\
V(t)&=tK(t)+\frac{K(t)}2\int_0^{\ell(t)}D(s)\,ds,\\
A_{\rm near}(t)&=\int_0^{\ell(t)}D(s)\left(H_t(s)-\frac{K(t)}2\right)ds,\\
P(t)&=V(t)+A_{\rm near}(t)-C_{\rm out}(t).
\end{aligned}
$$
At a guarded zero $t>20$, meaning $D(t)=0$ and $D\ge0$ on $[0,t]$, the source estimates give a strictly positive excess $C_{\rm out}(t)-V(t)$. Consequently
$$
\left[
\forall t>20,\ D(t)=0,\ D|_{[0,t]}\ge0
\Rightarrow C_{\rm out}(t)\le V(t)
\right]
\Longleftrightarrow
\left[\forall t>0,\ D(t)>0\right].
$$
See `liEvenCrossActualClockHistory_first_zero_budget_iff_pos` in [LiEvenCrossActualClockScoreBudget](../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockScoreBudget.lean).

The obstruction is particularly sharp. If $Z_S$ denotes the guarded-zero set, then
$$
\mathrm{RH}\Longleftrightarrow Z_S=\varnothing.
$$
Under false RH, $Z_S$ has a final point $\tau$, the first entrance into negative history. Its analytic order is odd; earlier guarded zeros have even order at least two. Yet $Z_S$ is **unconditionally finite**, hence bounded above. Therefore an eventual guarded-zero budget is unconditionally vacuous beyond some cutoff. It cannot establish RH. The needed budget must exclude every possible guarded zero, including those in the bounded region whose location is not supplied by the boundedness theorem.

These are `liEvenCrossActualClockGuardedZeroSet_rh_iff`, `liEvenCrossActualClockGuardedZeroSet_ordered_of_not_rh`, `finite_liEvenCrossActualClockGuardedZeroSet`, and `exists_forall_ge_not_mem_liEvenCrossActualClockGuardedZeroSet` in [LiEvenCrossActualClockTerminalHistory](../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockTerminalHistory.lean). Positive repeated Borel primitives and local terminal-mass asymptotics do not discharge this universal history budget.

**Suzuki and CCM: semibounded completed sources, with precise transport obstructions.**

For any fixed $L>0$, define the rectangular Ward defect
$$
\mathcal W_{L,E}(n)
=\operatorname{Re}\bigl(\mathrm{xiScrewWindowCurvature}(L,\log n)\bigr)-E(n).
$$
For any $E(n)\ge0$, the existence of $B,N_0$ with
$$
\mathcal W_{L,E}(n)\ge B
\quad(n\ge N_0,\ L\le\tfrac12\log n)
$$
implies RH. Under false RH, for every such $E$, every real $B$, and every $N_0$, an admissible $n\ge N_0$ has $\mathcal W_{L,E}(n)<B$. This is cofinal unboundedness below, not a claimed limit to $-\infty$.

Thus exact equality with a positive Gram is stronger than the receiver requires. A source decomposition with nonnegative bulk and an endpoint term uniformly bounded below suffices. See `riemannHypothesis_of_suzukiRectangularWardDefect_eventually_bddBelow` and `riemannHypothesis_of_suzukiRectangularWardDefect_bulk_endpoint` in [SuzukiRectangularWardDefectBoundedness](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiRectangularWardDefectBoundedness.lean).

There is an actual finite-source positive completion. With the bare wall field $\omega$, define
$$
\ell_\pm(t)=\frac{\omega(t)\pm i\omega(-t)}2.
$$
For every finite prime-power packet and every finite height packet,
$$
F_{\rm reflected}+\operatorname{Gram}(\ell_-)
=\operatorname{Gram}(\ell_+),
$$
and both Gram matrices are positive semidefinite. The difference need not be positive. This is `suzukiCriticalWallReflectedCurrentPacketMatrix_add_negative_eq_positive` in [SuzukiWallFieldLightConeKernelCompletion](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiWallFieldLightConeKernelCompletion.lean).

The transfer to the complete rectangular source must respect three exact obstructions:

- The bare critical prime amplitude has no nonzero constant multiple in $\ell^2$. Its squared mass is the nonsummable critical prime source.
- The depth-fused response satisfies a bound $C(h)\omega_p/(p+1)$. At the moving prime wall the sharp rectangular gate is one, and no uniform constant recovers $\omega_p$ from that response.
- A real linear functional on **all** prime-coordinate functions extending the finite critical source sums is unbounded below on the nonnegative coordinate cone. A universally positive finite-part extension on that domain is impossible.

See [SuzukiCoherentSharpSourceDomainNoGo](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCoherentSharpSourceDomainNoGo.lean), [SuzukiCoherentResponseGainNoGo](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCoherentResponseGainNoGo.lean), and [SuzukiCofinalPositiveFinitePartNoGo](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCofinalPositiveFinitePartNoGo.lean). These statements constrain the source domain and the transfer norm. They do not exclude a completed signed estimate on a restricted domain. The target is a lower bound for the actual assembled Ward defect, with the light-channel cost and the archimedean, boundary, and mixed terms retained.

The CCM first-clock source has a similarly weak exact endpoint:
$$
\mathrm{RH}\Longleftrightarrow
\exists C\ge0,\ A\ge\pi/2,\ \forall L\ge A,\quad
\mathrm{ccmPublishedSourceSineCoefficient}(L/2,2\pi/L)\ge-C.
$$
False RH forces this source below every constant on every tail. See `ccmFirstClockPublishedSourceEventuallyBoundedBelow_iff_rh` in [CCMFirstClockTailLowerBoundCompleteness](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockTailLowerBoundCompleteness.lean).

Positive mixing is classified, rather than supplied:

- On an injective finite prime-power packet, a real matrix preserving the actual source and commuting with all physical phase diagonals is exactly the identity, including when signed matrices are allowed.
- For nonnegative weights $w$ of positive total mass, an oriented source-faithful Markov transport exists exactly when the original scalar $w\cdot s$ is nonnegative. Universal feasibility for the completed physical packets is equivalent to RH.

See [CCMFirstClockPhaseNaturalTransportRigidity](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockPhaseNaturalTransportRigidity.lean) and [CCMFirstClockBarycentricOrientationCompleteness](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockBarycentricOrientationCompleteness.lean). An arbitrary positive mixer at each aperture supplies no independent estimate. The first-clock source lower bound is the mathematical obligation.

**Arithmetic index descent and conjugate-diagonal geometry: substantial reserves and explicit remaining costs.**

For the complete coarse/detail profile $F$, the nonfirst polar source satisfies, for every $\varepsilon>0$, after a fixed detail head,
$$
(1-\varepsilon)\Gamma(F)+2C(F)^2
\le \mathcal S_{\rm nonfirst}(F)+2S(F)^2.
$$
The head depends on $\varepsilon$; the estimate then holds for all coarse coefficients, all permitted detail coefficients, and every section horizon. Here $\Gamma$ is the Lévy/Gamma energy and $C,S$ are the cosh and sinh half-moments.

Restoring the entire square source yields a joint reserve
$$
c\Gamma(F_{\rm coarse})
+\frac\gamma2\|F_{\rm coarse}\|_2^2
+\frac{\mathrm{gap}}8\,\mathrm{haarLogMass}(F_{\rm detail})
+\|F_{\rm detail}\|_2^2+2C(F)^2
\le
\mathcal S_{\rm square}(F)+2S(F)^2+\frac12\left(\int F\right)^2
$$
for some $c>0$ and fixed detail head, where $\gamma$ is Euler's constant. Its exact source expansion contains
$$
\Gamma(F)+2\,\mathrm{gammaHardyPhaseRate}(0)\|F_{\rm detail}\|_2^2
-(\mathrm{haarPrimeEnergy}-\mathrm{squarePrimeSource}(F_{\rm detail}))
-\mathrm{squarePrimeSource}(F)
-\mathrm{oddHigherPrimePowerMixedSource}
+2C(F)^2-2S(F)^2.
$$
This is a specific completed subform, not full Weil positivity. The remaining comparison must keep the coarse and mixed prime terms, the finite head, and the displayed mass and moment costs.

Lean anchors: `exists_fullPolarNonfirst_completeGamma_reserve` in [TheFullNonfirstSourceRetainsAlmostAllGamma](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheFullNonfirstSourceRetainsAlmostAllGamma.lean); `exists_fullSquarePolar_coarse_detail_reserve` and `fullSquarePolarSourceForm_eq_source_parts` in [TheEntireSquareSourceSharesTheFullDetailReserve](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheEntireSquareSourceSharesTheFullDetailReserve.lean).

There is also actual prime–polar cancellation in Gamma norm:
$$
|\mathrm{primeSum}(u)-(2C(u)^2-2S(u)^2)|
\le\varepsilon e^{S/2}\bigl(\Gamma(u)+\|u\|_2^2\bigr)
$$
eventually in $S$, uniformly over core tests with $2\,\mathrm{supportRadius}(u)+1\le S$. The exponential factor is part of the theorem; it cannot be discarded when seeking positivity. See `eventually_primePolar_gamma_bound_core` in [TheFullPrimePolarSourceCancelsInGammaNorm](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheFullPrimePolarSourceCancelsInGammaNorm.lean).

For conjugate-diagonal geometry, the positive metric $D$ has exact defect
$$
\mathrm{Def}_L(f)=D(T_Lf)+D(T_{-L}f)-2D(f)
\ge4L^2\,\mathrm{depthSecondMoment}(f).
$$
Its explicit theta approximation is uniform in moving parameters: for fixed compact $f$, every $\varepsilon>0$, all sufficiently large $n$, and
$$
|\tau|\le n/2,\qquad |L|\le2\log(n+1),
$$
the finite theta source evaluates $\mathrm{Def}_L(\mathrm{sourceTwist}_\tau f)$ within $\varepsilon$. The arithmetic reconstruction, including this moving range, is established. A depth exclusion still needs a sufficiently small upper bound for the actual defect.

See `heckeDefect_eq_second_difference` in [ZetaDepthDistribution](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/ZetaDepthDistribution.lean) and `finiteThetaSource_uniform_moving_heckeDefect` in [FiniteThetaMetric](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/FiniteThetaMetric.lean).

**Index theory: classification and height localization are established; an arithmetic ceiling is a separate theorem.**

The zeta orbit kernel satisfies
$$
\operatorname{negIndex}(K_\zeta)
=\#\{\text{distinct right-of-line zeros}\}
=2\,\#\{\text{zeros in the selected right-hand sector}\},
$$
with extended cardinalities. The count is of locations, not multiplicities. Every two-distinct-prime lattice has the same index. Finite index is equivalent to finite off-line support, a uniform finite bound for the heated nonreal-zero count, and RH above some height. It implies the critical-line Lindelöf bound.

For every tempered zero configuration and every admissible real test,
$$
\mathrm{IsKreinLanger}(\mathrm{orbitKernel})
\Longleftrightarrow
\operatorname{negIndex}(\mathrm{orbitKernel})<\infty.
$$
There is no finite-total-spectral-support premise. These are [TheFiniteIndexStratumOfZetaIsLindelofDeep](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean) and `isKreinLanger_orbitKernel_iff_negIndex_lt_top` in [TheConverseKreinLangerTheoremForOrbitKernels](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheConverseKreinLangerTheoremForOrbitKernels.lean).

Height localization is also quantitative. Any finite prime set $P$ with
$$
|P|>\binom{\mathrm{heightIndex}(T)}2
$$
contains a prime whose tower, with a suitable compact $C^2$ generator and finite translation window, captures at least the entire height index. A two-prime certificate exists with
$$
0<k\le\left\lfloor T\log2/\pi\right\rfloor+1,\qquad
k\le j\le2k,
$$
and step $|\log(3^k/2^j)|$. See `exists_prime_certifies_height` and `twoPrime_tower_certifies_height` in [TheHassePrincipleWithHeights](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheHassePrincipleWithHeights.lean).

These are detection theorems. The generator and finite window remain existential, and the captured index is not bounded above by these statements. A source-side index ceiling, or an explicit positive family that forces one, is the remaining obligation. A uniform finite index bound for the **complete** kernel would be Lindelöf-strength; finite-index bounds for selected subforms do not supply it.

**Euler deletion: a cumulative covariance problem with an inner-cutoff constraint.**

For $1\le X<M$, write $L=\log(M/X)$. The actual averaged divisor coefficient is
$$
g_{X,M}(k)=\frac{b_M(k)-b_X(k)}L,
$$
where $b_Y$ is the corpus's Barban–Vehov coefficient. It satisfies $g(1)=1$, $g(k)=0$ for $1<k\le X$, and
$$
g(k)=\frac{\Lambda(k)-b_X(k)}L\qquad(1<k\le M).
$$
The modular quantity has an exact cumulative representation
$$
m_{X,M}(n)=\sum_{k\le n}g(k)-nH_{X,M}.
$$
Set $c(k)=\mathbf1_{k=1}-g(k)+H_{X,M}$, so $1-m(n)=\sum_{k\le n}c(k)$. Then
$$
\sum_{n=1}^T\frac{(1-m(n))^2}{n(n+1)}
=\sum_{j,k\le T}c(j)c(k)
\left(\frac1{\max(j,k)}-\frac1{T+1}\right).
$$
The full energy is this finite covariance plus the literal infinite tail. A coefficient square estimate for $g$, even with fixed-cutoff summability, is not an estimate for this cumulative covariance and its tail.

These identities and the actual coefficient estimates are in [EulerDeletionAveragedDivisorCovariance](../../../formal/GaloisForLFunctions/RHTower/EulerDeletionAveragedDivisorCovariance.lean), especially `errorEnergy_eq_covariance` and `fullErrorEnergy_eq_covariance_add_tail`.

The current criterion has a stringent normalization:
$$
\mathrm{RH}\Longleftrightarrow
\forall\rho,\ \forall e>0,\ \exists B,\ \forall K,\ \exists X<M,\quad
K\le X,\qquad
|\operatorname{Re}\overline J_{X,M}(\rho)|\le B X^e.
$$
Here $\rho$ ranges over actual nontrivial zeros. The outer cutoff may adapt; the power scale remains the **inner** cutoff $X$. See `riemannHypothesis_iff_averagedCurrent_cofinally_subpower` in [EulerDeletionCutoffAverage](../../../formal/GaloisForLFunctions/RHTower/EulerDeletionCutoffAverage.lean).

The source target is a covariance/tail estimate, or a direct current estimate, strong enough for this normalization. Enlarging $M$ and proving a bound in terms of $M^e$ does not meet it.

**Count precision and exact source rigidity are different requirements.**

Let
$$
\mathcal Q=\left\{\delta:\sum_{n\le x}\delta(n)
=O(\sqrt x\log^2x)\right\}.
$$
Here $\mathrm{Count}(a)$ means $\sum_{n\le x}a(n)-x=O(\sqrt x\log^2x)$. At any weight satisfying Count, its additive stabilizer is exactly $\mathcal Q$. Finite-support perturbations and $1/n$ belong to this class. In contrast, all-generator positivity on a fixed prime tower for $\Lambda+\delta$ is equivalent to RH together with
$$
\delta(n)=0\qquad(n\ge2).
$$
In particular, $\Lambda+1/n$ has Count iff RH and never has this tower positivity. See [PrecisionClassesAndTheCount](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/PrecisionClassesAndTheCount.lean) and [TowerPositivityIsPrecisionExact](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TowerPositivityIsPrecisionExact.lean).

The deciding-input theorem concerns a predicate $S$ on **all arithmetic weights** satisfying
$$
\forall a,\quad S(a)\Rightarrow\mathrm{Count}(a).
$$
It imposes precision and perturbation restrictions on such a predicate. It is not a classification of every possible RH proof or a theorem that every method must construct the same arithmetic object. See `deciding_input_necessary_properties` in [TheDecidingInputTheorem](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheDecidingInputTheorem.lean).

There is an exact integrality resource: the integrals over $[0,1]$ of integer polynomials of degree at most $n$ form
$$
\frac1{\operatorname{lcm}(1,\ldots,n+1)}\mathbb Z.
$$
The least positive integral is the reciprocal lcm, and its logarithmic reciprocal is $\psi(n+1)$. “Positive integral” imposes no pointwise nonnegativity condition on the polynomial. This lattice does not itself construct an auxiliary with the analytic size and arithmetic vanishing needed for a new count. See `isLeast_positive_nairIntegral` in [TheIntegralityLatticeOfTheHorizon](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheIntegralityLatticeOfTheHorizon.lean).

**Simple critical zeros: an unconditional proportion and an exact $75\%$ budget.**

The cumulative theorem gives, for every $\varepsilon>0$, eventually
$$
N_{0,\mathrm{simple}}(T)\ge(0.67250071-\varepsilon)N(T).
$$
This is `simple_critical_proportion_ge_67250071` in [CriticalLineZeroProportion](../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/CriticalLineZeroProportion.lean).

At bandwidth $4/3$, the signed coalescent receiver on $[T,2T]$ is
$$
N_{0,\mathrm{simple}}
\ge
\left(\frac{29}{36}-32\pi\varepsilon_1-\varepsilon\right)N
-\mathrm{CoalescentSurplus}(u,\eta,T)
+\mathrm{offLineMultipleMass}.
$$
The profile $u$, collar $\varepsilon_1$, and $\eta>0$ are the actual admissible parameters. A profile-existence theorem makes the collar loss arbitrarily small. See `zeta_coalescent_certificate_four_thirds_simple_and_offLineMultiple` and `zeta_coalescent_certificate_simple_and_offLineMultiple` in [ParitySensitiveRamanujanStabilizerTransfer](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/ParitySensitiveRamanujanStabilizerTransfer.lean).

With compatible windows and quantifiers, an upper surplus budget $bN+o(N)$ gives $29/36-b$. Therefore:

| Target for simple critical zeros | Sufficient surplus coefficient |
|---|---:|
| Strictly more than $2/3$ | $b<5/36$ |
| At least $70\%$ | $b\le19/180$ |
| At least $75\%$ | $b\le1/18$ |

The actual prime sum has an exact stabilizer-model-plus-discrepancy decomposition, `oddEvenShiftPrimeCoalSum_eq_stabilizerModel_add_discrepancy`. Model calibration at $4/3$ gives
$$
(1,0)\mapsto-1/144,\qquad
(1,1)\mapsto0,\qquad
(2,1)\mapsto1/16.
$$
More generally,
$$
(\Upsilon,0)\mapsto(9\Upsilon-10)/144,\qquad
(1+\Upsilon,1)\mapsto\Upsilon/16.
$$
The first family reaches $1/18$ exactly when $\Upsilon\le2$; the second requires $\Upsilon\le8/9$. See `calibration_five_models_four_thirds` in [CoalescentSieveAnatomyAndModelCalibration](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/CoalescentSieveAnatomyAndModelCalibration.lean).

If the actual stabilizer model has normalized limit $-1/144$, the remaining allowance for a $75\%$ theorem is $1/16$. The displayed model calculation does not establish that limit or the discrepancy bound for actual primes. The target is the signed estimate in the receiver's own windows, uniformly for all sufficiently large heights. A different window or a favorable subsequence is insufficient. Off-line multiple mass is a positive credit in this census, not a reason to identify near-line zeros with critical-line zeros.

**Quasi-RH: exact arithmetic energy targets and a separate detector budget.**

Let $\Theta$ be the supremum of zero real parts, and define
$$
S(M)=\sum_{2\le n<M}\frac{\psi(n)-n}{\sqrt n}.
$$
This is the literal `chebyshevNormalizedCesaroSum` in [NormalizedChebyshevCesaroAndSqrtRieszBridge](../../../formal/GaloisForLFunctions/RHTower/NormalizedChebyshevCesaroAndSqrtRieszBridge.lean). Either $S(M)\le CM$ for all $M\ge3$, or the corresponding lower bound, is equivalent to RH. Its cumulative normalized energy is
$$
\mathcal E(N)=\sum_{M=2}^N\left(\frac{S(M)}M\right)^2.
$$
The corpus proves
$$
2\Theta=\inf\{r\ge1:\ \exists C\ge0,\ \forall N\ge2,\ 
\mathcal E(N)\le CN^r\}.
$$
In particular,
$$
\begin{aligned}
\{\rho:\xi(\rho)=0\}\subseteq[1/6,5/6]+i\mathbb R
&\Longleftrightarrow
\forall\varepsilon>0,\quad\mathcal E(N)\ll_\varepsilon N^{5/3+\varepsilon},\\
\{\rho:\xi(\rho)=0\}\subseteq[1/4,3/4]+i\mathbb R
&\Longleftrightarrow
\forall\varepsilon>0,\quad\mathcal E(N)\ll_\varepsilon N^{3/2+\varepsilon}.
\end{aligned}
$$
A one-sided bound for $S(j^m)/j^m$ on any fixed power mesh $m\ge1$, with exponent $c$, already gives $\Theta\le1/2+\max(0,c)$. Either an upper or a lower bound suffices. These are arithmetic source targets, not consequences of the dictionary itself. See [QuasiRHNormalizedChebyshevCesaroAndMertensActionAbscissaLaw](../../../formal/GaloisForLFunctions/RHTower/QuasiRHNormalizedChebyshevCesaroAndMertensActionAbscissaLaw.lean), especially the exact mean-square abscissa law and the two strip equivalences.

The detector Gram optimization is a different statement. For its exponent model $B(x,s;\nu,\kappa)$, with $\nu\ge0$,
$$
\exists x\ge0,s:\ B(x,s;\nu,\kappa)\le5/6
\Longleftrightarrow
\nu\le1/15,\qquad \kappa+4\nu\le4/3.
$$
A feasible witness is
$$
x=5/48,\quad s=1/6,\quad\nu=1/30,\quad\kappa=6/5.
$$
Leaving the ordinary contribution at $\kappa=2$ prevents a five-sixths budget, regardless of the exceptional contribution. With the exceptional contribution removed, the optimized ordinary budget is $23/27$. Even the unit-Gram budget has minimum $29/36>3/4$. Thus a three-quarters result requires changing another term in this detector architecture or using a different source estimate.

These are `gramProfile_five_sixths_feasible_iff`, `ordinaryGramBoundary_sharp_minimum`, and `unitGramBoundary_sharp_minimum` in [QuasiRHDetectorGramTradeoff](../../../formal/GaloisForLFunctions/RHTower/QuasiRHDetectorGramTradeoff.lean). The identity $B(17/48,1/6;1/6,2)=7/8$ is a budget evaluation. None of these optimization statements supplies the corresponding actual Gram estimate or, by itself, an unconditional zero strip.

**The missing theorems are source-specific.**

| Source | Mathematical obligation | Result it would support |
|---|---|---|
| Overlapping atomic Weil form | Completed macroscopic comparison; conductor and horizon control; profile-compatible exhaustion | Larger fixed-overlap positivity, then an RH-complete family |
| Signed theta jets | All-order native-form or Schur-complement positivity | Complete Hankel cone and RH |
| Actual theta-clock history | Budget at every possible guarded zero | Positive history and RH |
| Suzuki rectangular source | Uniform lower bound after complete source assembly on the correct domain | RH |
| CCM first-clock source | A constant lower bound on every sufficiently large physical aperture | RH |
| Arithmetic index | Upper control of the complete index, beyond height detection | Finite off-line support and Lindelöf; index zero gives RH |
| Euler deletion | Cumulative covariance and infinite-tail control at inner-cutoff scale | The cofinal current criterion |
| Signed coalescent source | Actual normalized surplus at most $1/18$, with compatible windows | $75\%$ simple critical zeros |
| Chebyshev energy / detector Gram | Actual energy estimate, or both required Gram improvements | A specified zero strip |


**The top three research questions.**

The ranking below is a research judgment based on three criteria: an actual source, an exact remaining expression, and a substantial conclusion from a bounded intermediate theorem. It does not assign probabilities of proving RH.

1. **Can the signed theta hierarchy propagate positivity through its native successor integrals?**

   For $0<a<1/2$, put
   $$
   I_n(a)=\int_0^\infty r\sinh(ar)\,
   \mathrm{thetaCuspNativeSuccessorSource}(a,n,r/2)\,dr.
   $$
   The concrete question is whether source identities yield $I_n(a)\ge0$ whenever the preceding section is strict, with a mechanism that preserves strictness or controls the radical at subsequent steps.

   The first test is $I_7(a)$: the full rank-seven head is positive definite, and the successor theorem identifies exactly what an eighth section requires. A useful advance would explain the sign through a reusable source compensation, rather than furnish only another isolated numerical order. An all-order theorem would give RH; a uniform finite-order extension would enlarge an actual positive part of the deciding hierarchy.

   This takes first place because the source, the signed hierarchy, the strict initial section, and the next residual are all explicit. The main uncertainty is whether the compensating structure persists with order. Neither global three-node positivity nor positivity of unsigned moments answers that question.

2. **Does the cyclotomic Gram control the completed Weil operator at macroscopic overlap?**

   Seek eventual nonnegativity at $c=3/2$ for a fixed nondegenerate profile, with quantitative dependence on conductor and horizon. The first theorem should identify the completed successor-shell action as a cyclotomic Gram contribution plus an explicit residual, account for its cyclotomic radical, and bound the cross-annulus and Schur terms in the actual coefficient norm.

   The divisor-family identity $Q\min(i,j)-ij$ supplies a concrete comparison kernel. Uniform affine averaging and arbitrary coefficient packets at fixed modulus supply the averaging input. The logarithmic row growth forces the comparison to retain signed completion; the sharp scalar certificate rules out gaining macroscopic overlap by rearranging its existing inequalities.

   Success at one macroscopic ratio would establish a new complete-form positivity range. RH additionally requires a compatible profile and simultaneous control along an exhausting overlap schedule. This question ranks ahead of a generic count-construction programme because its missing operator is more tightly specified by established arithmetic structure.

3. **Can the actual signed coalescent surplus meet the $1/18$ budget?**

   Prove the surplus bound for the same admissible bandwidth-$4/3$ profiles and all sufficiently large heights. A concrete decomposition target is a proved model limit $-1/144$, together with normalized signed discrepancy at most $1/16$, including collar and truncation costs. The $19/180$ surplus threshold provides a $70\%$ checkpoint.

   This question permits exceptional zeros while retaining a simplicity requirement and a precise quantitative allowance. Its decisive uncertainty is an estimate for the actual centered prime source; model calibration and unsigned upper bounds in the displayed affine model classes do not provide it. Success gives a simple-critical census improvement without requiring a complete positivity theorem or an index ceiling.

The Suzuki and CCM lower bounds, the theta-clock budget, and Euler-deletion covariance remain distinct alternatives. Their exact endpoints deserve direct source estimates; no theorem above reduces them to the overlap question. For a strip-specific objective, the Chebyshev energy exponents and the detector feasibility region give concrete targets. A one-sided count construction remains valuable, with its correct error class $\mathcal Q$, but the integrality lattice alone does not identify the analytic estimate that would produce it.

A route can bypass a particular obstruction by using a different source quantity or domain. The Metzler obstruction, the positive-extension obstruction, and Markov-mixing rigidity each have specified scopes. They do not classify every possible RH proof. The mathematical basis for considering different routes is this diversity of exact source problems, not a claim that an unrestricted new representation will force positivity.

**The proposed field: a quantitative theory of completed arithmetic forms.**

This is a proposed organizing programme. Its central problem is:

> Which relations in an explicit arithmetic or theta source produce a lower bound for its completed form, and preserve that bound through the precise compression, accumulation, or limit required by the endpoint?

EffectiveArithmeticHodgeTheory, CriticalArithmeticCorrelationTheory, ArithmeticIndexDescent, and ArithmeticOfSquareRootPrecision supply parts of this theory. The height Hasse theorem and the orbit-kernel converse Krein–Langer theorem belong to its established foundation. The signed theta hierarchy, causal clock equations, and cumulative covariance show that its objects must extend beyond prime-lattice kernels.

An object should specify an actual source, its natural domain, its complete signed form, its positive comparison form, the comparison radical, and the parameter range. The endpoint determines which estimate matters: positivity, a constant lower bound, an index bound, a count modulo $\mathcal Q$, or a census allowance. These requirements cannot be replaced by a single universal sign axiom.

The key mathematical tools would be:

| Tool | Established model | Missing research content |
|---|---|---|
| Coercivity modulo an arithmetic radical | Cyclotomic divisibility and the exact divisor bridge | Control of the actual shell residual on the quotient and on its null directions, across annuli and growing conductors |
| Successor estimates for signed source forms | Strict rank seven and the native Schur integral | A source compensation valid as rank grows, including strictness or radical control |
| Completion on a specified domain | Finite Suzuki light-Gram identity; impossibility of a positive extension on all coordinates | A complete source lower bound on the domain used by the rectangular receiver |
| Estimates after accumulation | Exact Euler-deletion kernel $1/\max(j,k)-1/(T+1)$ | Arithmetic control of unequal-pair covariance and the infinite tail at inner-cutoff scale |
| Precision-preserving source transfers | Count stabilizer $\mathcal Q$; exact tower rigidity; moving theta reconstruction | Comparisons that retain the endpoint's error tolerance and simultaneous parameter range |
| Signed census dispersion | Stabilizer decomposition and exact model budgets | A prime-source discrepancy bound with the required centering, parity, and constant |

Three principles make this a mathematical programme with testable content.

First, **positive pieces must be compared with the original completed object**. The theta successor subtracts a Schur cost; the Suzuki reflected current is a difference of two positive Grams; index descent retains explicit polar and mass costs. Each needs its own comparison inequality. Reusing a positive reserve in two subtractions requires a joint bound.

Second, **the domain and the quantifiers belong to the theorem**. The Suzuki extension no-go acts on all coordinate functions; a restricted completed domain is a different problem. The clock's finite guarded-zero set requires exclusion everywhere, whereas CCM's first-clock receiver needs only an eventual constant lower bound. Fixed-conductor uniformity over all coefficients still leaves conductor growth. These distinctions specify different estimates, not different presentations of one estimate.

Third, **precision is attached to the observable**. Exact source rigidity is appropriate for complete tower positivity. The count permits $\mathcal Q$-perturbations. The census permits an aggregate surplus. Euler deletion permits adaptive outer cutoffs but measures growth at the inner cutoff. A useful transfer theorem states what each operation preserves and what it costs.

A foundational result for this programme would prove one of the comparison inequalities in the table directly from the actual source, with a reusable mechanism and its full parameter range. The top three questions supply concrete tests: a theta successor compensation, a macroscopic completed overlap comparison, and a signed census estimate. The broader field would be built from such theorems; neither a name nor an abstract realization supplies their missing inequalities.

# Arithmetic Orientation Geometry (AOG)

Namespace `GaloisForLFunctions.ArithmeticOrientationGeometry` (sub-namespace `ScalingDatum`);
umbrella `ArithmeticOrientationGeometry.lean`; 19 modules.

## 1. Motivation

Weil's proof for curves gets the sign from the Frobenius graph: Castelnuovo–Severi on the plane of
graph and diagonal is the Hasse–Weil bound. The scaling flow of $\mathbb Z$ has graphs, Lefschetz
numbers, adjunction and a Rosati involution of the same shape, but no proof of the inequality. AOG
abstracts this to a **scaling datum** and works one orbit at a time: which cycles does the scaling
correspondence orient, what decides it, and which arithmetic structures provably cannot. AOT orients
sources; AOG orients correspondences.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Scaling datum | `ScalingDatum G E`, `zetaScalingDatum`, `configScalingDatum` | polar surface + isometric scale action, fibres weighted $e^{\pm s/2}$ |
| Orbit correlation | `orbitCorr` | $c_x(g)=\delta(\psi_gx,x)$, primitive Lefschetz trace |
| Lefschetz number | `lefschetz`, `heckeGraph`, `heckeGraphRosati` | $L(x,g)=e^{s/2}\,\psi_gx\cdot x$ |
| Hasse–Weil | `HasseWeilAt` | $|c_x(g)|\le c_x(0)$ |
| Orbit Hodge index | `OrbitHodgeIndex`, `orbitComb` | $c_x$ positive-definite on $G$ |
| Correspondences | `Correspondence`, `corr`, `conv`, `rosati`, `traceAt`, `RosatiPositive` | measures on $G$; $\xi'(g)=\xi(-g)$ |
| Configuration surface | `configWeil`, `configSurface` | defect = zero-side Weil form of a tempered configuration |
| Blindness | `BlindOffLine`, `BlindAbove`, `Sees`, `RealSpectrallyGeneric`, `OffLineGeneric` | transform zeros at $\gamma_\rho,\bar\gamma_\rho$ |
| Seen zeros | `seenConfig`, `seenRightZeros` | zeros a test sees |
| Orbit/family surfaces | `orbitSpan`, `orbitSurface`, `FibreCompatible`, `familySurface` | restriction to an orbit/family |
| Families | `ScaleStable`, `JointlySees`, `orientedSubspace`, `orbitFamily` | translate-closed test spaces |
| Correctors | `lefschetzTrace`, `poleTrace`, `primTrace`, `IsCorrector`, `damp`, `dampedEnergy` | zero pole trace; $E_x(\varepsilon)=\sup e^{-\varepsilon t}|c_x(t)|$ |
| Theta $h^0$ | `thetaSum`, `arithH0`, `poleH0` | $h^0(d)=\log\sum e^{-\pi n^2e^{-2d}}$ |
| Euler deletion | `roughMoebius` | $\mu_\varepsilon$ prime to a finite set |
| Index exit | `rightCopies`, `offLineCopies`, `xiMult` | multiplicity copies of zeros of $\xi$ |
| Spline cycle | `splineCycle` | cubic spline $B=U_1^{\star4}$, $\hat B=(\sin z/z)^4$ |
| Battery | `goldenConfig`, `goldenDepth`, `curveShiftedPair`, `shiftedPairConfig` | impure models |

## 3. Language

- **Oriented** cycle: Hasse–Weil at every scale ⇔ orbit Hodge index.
- **Sees** $\rho$: transform nonzero at both $\gamma_\rho$ and $\bar\gamma_\rho$. **Blind** off-line: misses one
  point of every off-line pair. **Blind above** $\sigma$: same for zeros of depth $>\sigma$.
- **Orientation rate**: growth exponent of $c_x(t)$. **Orientation index**: negative squares on the orbit.
- **Generic** test: transform nonzero at every zero (or every off-line zero: off-line generic).
- **Soft structure**: identities that hold on every scaling datum, including impure ones.
- **Corrector**: correspondence with zero pole trace $\sum\xi(g)(e^{s(g)}+1)=0$.

## 4. Mechanisms

**Identities (no sign).**
1. Lefschetz $L=(e^s+1)(x\cdot H)(x\cdot V)-e^{s/2}c_x(g)$; Lefschetz–adjunction
   $L-\tfrac{e^s+1}2x^2=\tfrac{(\sigma-1)^2}2\delta(x,x)+\tfrac\sigma2\delta(\psi_gx-x)$.
2. Weil plane: defect on $\langle\psi_gx,x\rangle$ is $(r^2+t^2)\delta(x,x)+2rt\,c_x(g)$; Hasse–Weil ⇔
   Castelnuovo–Severi on $\langle H,V,\psi_gx,x\rangle$ ⇔ Lefschetz bound.
3. Orbit defect = Toeplitz form in $c_x$; globally HI ⇔ every cycle HW at scale 0 (all scales add nothing
   globally; per cycle they do).
4. Correspondences: $\delta(\xi x,\eta x)=\tau_x(\xi\star\eta')$; Rosati positivity at $x$ = orbit Hodge index;
   $\Gamma_g\cdot\Gamma_h=e^{s(h)}L(x,g-h)$, $\Gamma_g^2=e^{s}x^2$, $TT'=e^s$.
5. Configurations: translation multiplies the summand at $\rho$ by $e^{(s-t)(\rho-\frac12)}$, so
   $c_f(t)=\operatorname{Re}\sum_\rho e^{t(\rho-\frac12)}w_\rho(f)$; for $\zeta$ the configuration surface is the
   scaling surface of $\mathbb Z$ (explicit formula).

**Orientation = blindness = growth.**
6. Blind cycles are oriented on every configuration; on FE-symmetric ones Hasse–Weil at every scale forces
   blindness (a seen right zero is a top pole of the Laplace transform; two-bump minor fails).
7. Rate theorem: $|c_f(t)|\le Ke^{\sigma t}$ ⇔ blind above $\sigma$. Eventual bounds upgrade: bounded at large
   scales (any constant) ⇒ sharp Hasse–Weil everywhere.
8. Damping: $E_x(\varepsilon)<\infty$ ⇔ blind above $\varepsilon$; finiteness for every $\varepsilon>0$ (any
   constants) gives $E_x(\varepsilon)=c_x(0)$ — no damping-uniform control needed. Damping is an automorphism
   of correspondences but conjugates Rosati to the opposite damping.
9. Index: on the orbit of $f$ the Weil form is that of the zeros $f$ sees; negative squares on translates =
   seen right zeros (no FE symmetry needed); orbit signature = $1+$ seen right zeros.
10. Families: joint seeing = seeing by one member; scale-stable family oriented ⇔ jointly blind ⇔ inside an
    oriented subspace of a choice; index = jointly seen right zeros. Two cycles blind at opposite points span
    a family that sees the zero: orientation is not additive.
11. Sections: orbit-span classes = pole plane + correspondence image; RR on an orbit/family surface ⇔ open
    positive cone ⊆ cone ∧ oriented.

**Deciding orbits and quantitative readings.**
12. One generic orbit decides the line; generic tests exist (bad dilations countable). The cubic spline is
    off-line generic on every configuration, so its single orbit decides RH, reads the zero width, and its
    prime-side Weil Gram negative index counts distinct right zeros — already on the two-prime Hecke orbit
    $k\log p+l\log q$. Right zeros pair up, so index $\le1$ ⇔ RH.
13. Curves: narrow tests read traces on the $q$-tower, $c_f(\nu\log q)=\log q\,\|f\|^2\operatorname{tr}F^\nu$;
    Turán's second main theorem gives a violation in every window of $2g$ scales with explicit constant.
14. Archimedean place: tests vanishing at the pole and on the low grid of aperture $a+T/2$ are oriented on
    the segment $|t|\le T$; no nonzero test meets all grids (they become dense).
15. Euler factors: deleting finitely many from $\mu_\varepsilon$ is convolution by a unit — payment, ideal, hull
    unchanged; $\mu_\varepsilon$ is a unit for $\varepsilon>\tfrac12$ and leaves the algebra for $\varepsilon\le\tfrac12$.
16. Base RR: $h^0(d)-h^0(-d)=d$ by Poisson; $\Lambda(s)$ is the Mellin generating function of $e^{h^0}-1$;
    pole-plane RR $h^0(D)-h^0(D^\vee)=\log(D^2/2)$.
17. Index exit: if $D<\infty$, collision mass of the de Bruijn–Newman flow after small $t$ equals $2(D+E)$,
    $E$ the multiplicity excess; uniform bounds on any attached count ⇔ finitely many off-line zeros
    (⇒ $\Theta<1$, short-window savings); $D$ is even, so RH ⇔ $D<2$.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Weil planes; global equivalences | `hasseWeilAt_iff_castelnuovoSeveri_weilPlane`, `hodgeIndex_tfae` | unconditional |
| Rosati = orbit Hodge index | `rosatiPositive_iff_orbitHodgeIndex` | unconditional |
| Orbit correlation = exponential sum over zeros | `configScalingDatum_orbitCorr_eq`, `configSurface_zeta_eq` | unconditional |
| Orientation theorem | `orientation_tfae`, `zeta_orientation_iff` | unconditional |
| Rate = deepest seen zero | `orbitCorr_rate_iff_blindAbove`, `zeta_orbitCorr_rate_iff_zetaZeroWidth_le` | unconditional |
| Eventual = sharp; lossless damping | `hasseWeilAt_of_eventually_bounded`, `dampedEnergy_tfae` | unconditional |
| Orientation index law | `orientationIndex_law`, `zeta_orbit_signature_law`, `scaleStable_index_law` | unconditional |
| RR on orbits = orientation | `orbitSurface_riemannRoch_iff`, `familySurface_riemannRoch_iff` | unconditional |
| Spline orbit decides RH | `riemannHypothesis_iff_splineOrbit_hasseWeil`, `riemannHypothesis_iff_splineTwoPrime_negIndex_eq_zero` | equivalences |
| Archimedean segment orientation | `orbitSegment_defect_nonneg_of_lowBlind`, `eq_zero_of_lowBlind_forall` | unconditional |
| Euler tail law | `receiverBounded_roughMoebius_iff`, `not_criticalWiener_moebius` | unconditional |
| Base RR of Spec ℤ | `arithH0_riemannRoch`, `completedRiemannZeta_eq_mellin_arithH0` | unconditional |
| Index exit | `eventually_collisionMassAfter_eq`, `index_exit_first_rung_tfae`, `riemannHypothesis_iff_encard_rightZeros_lt_two` | unconditional |
| Soft structure does not orient | `golden_soft_structure_and_disorientation` | unconditional |

## 6. Tools

**Developed.**
- Scaling-datum calculus: defect invariance, adjoint $\psi_{-g}$, orbit combinations, Weil planes.
- Correspondence algebra with Rosati involution, traces, Hecke graphs, damping automorphisms.
- Configuration surfaces for any tempered zero configuration; translation law; reality of $W$ on
  FE-symmetric configurations.
- Seen/jointly-seen configurations; generic and off-line generic tests; dilation genericity.
- Orbit and family surfaces via `PolarSurface.restrict`.
- Damped orbit energy; damped correctors on any two scales.
- Turán power-sum lower bound on curve towers; theta $h^0$ with Poisson RR.
- Index-exit dictionary to de Bruijn–Newman collisions and horizontal collision charges.

**To build.**
- A surface $h^0$ for classes with a test component and an RR proved without the sign (base RR exists).
- A quantitative reading over $\mathbb Z$ (infinitely many terms) analogous to Turán on curves.
- A source bound on the heat-collision index uniform as $t\to0$.
- Cheaper archimedean orientation of segments, or a proof that doubly exponential cost is necessary.
- An estimate on infinitely many Euler factors that repairs $\mu_\varepsilon$ below $\tfrac12$.

## 7. Open questions

1. Subexponential growth of the single explicit function $t\mapsto W(B,B(\cdot-t))$ (equivalent to RH): which
   arithmetic input controls it?
2. An independent RR on orbit surfaces (the theorem shows RR there is equivalent to orientation).
3. The shifted pair and parity twins over $\mathbb Z$ as configurations (zeros $\rho\pm a$ leave the strip).
4. Is the doubly exponential archimedean cost of orienting a length-$T$ segment necessary?
5. Which properties of infinitely many Euler factors repair $\mu_\varepsilon$ in $0<\varepsilon\le\tfrac12$?
6. A first-rung bound: finiteness of the collision index from a source estimate.
7. Index laws for families that are not scale-stable.

## 8. Traps

| Trap | Truth |
|---|---|
| Lefschetz, adjunction, pullback, $TT'=e^s$ orient | Hold on every scaling datum, including golden |
| All scales stronger than scale 0 | Globally equivalent (`hodgeIndex_tfae`); different only per cycle |
| Weil's second proof avoids Hodge index | Rosati positivity at $x$ = orbit Hodge index |
| Orientation is a sign condition | On configurations it is a growth condition on $c_x$ |
| Positive prime counts, integrality, FE orient | Golden datum has all and is disoriented |
| Multiplicity bounds help orientation | Orientation depends only on the zero set (`orientation_congr_carrier`) |
| Height averages read clusters | Windowed forms blind; one generic orbit reads the depth |
| Orientation is additive | Opposite blindnesses span a seeing family |
| Damped bounds lose energy as $\varepsilon\downarrow0$ | Lossless on orbits; finiteness is the whole content |
| One explicit deciding orbit makes RH easy | Proving its orientation is RH |
| Euler products decide repair | Only for $\varepsilon>\tfrac12$; finite truncations invisible below |
| Archimedean place orients a cycle | Only finite segments; no test is blind on all grids |
| Base theta RR gives the Hodge index | It gives the functional equation; surface RR is missing |
| Bounded collision mass = RH | Equivalent to finitely many off-line zeros |
| One negative square possible | Right zeros pair; index jumps 0 → 2 |

## 9. Context

| Direction | Programmes (module imports) |
|---|---|
| Uses | ArithmeticCastelnuovoSeveri 14, SquareRootThreshold 5, RHTower 5, BezoutValuationIncidence 2, HTGeometry 1, ArithmeticOrientationTheory 1 |
| Used by | HeckeKreinToeplitz 4, SpacingScaleHarmonicAnalysis 2, ArithmeticEffectivityTheory 2, ArithmeticCorrespondencePositivity 2, ArithmeticCastelnuovoSeveri 2, EffectiveArithmeticHodgeTheory 1, ArithmeticPositiveDuality 1, MainTheorems |

| Neighbour | Interface |
|---|---|
| ArithmeticCastelnuovoSeveri | polar/scaling surface, curve data, cyclic Pontryagin law, universal floor law, low-grid positivity |
| SquareRootThreshold | tempered configurations, two-bump minors, top-pole lemmas, cluster windowed blindness, zero width |
| ArithmeticOrientationTheory | Wiener-algebra payment for Euler-deletion law; AOT orients sources, AOG correspondences |
| RHTower | de Bruijn–Newman collisions, horizontal collision charge, cross-route bridges |
| BiScaleUncertainty | cubic spline and its transform |
| HeckeKreinToeplitz, ArithmeticPositiveDuality | consume spline/Hecke orbits and orbit kernels |

## 10. Big picture

AOG shows that the sign Weil needed is, cycle by cycle, positive definiteness of one function on the scale
group, and that this function is an exponential sum over the zeros. Every geometric identity of Weil's
proof survives on impure models, so none can supply the sign; every soft arithmetic property (integrality,
functional equation, positive prime counts) survives on the golden curve, so none can either. What decides
orientation is purely spectral: a cycle is oriented exactly when it is blind to the off-line zeros, its
growth rate is the depth of the deepest zero it sees, and its negative index counts the right zeros it sees.

For the RH programme this collapses many formulations into one explicit target: the translation orbit of
the cubic spline. RH is equivalent to Hasse–Weil along that orbit, to subexponential growth of one function
computed from primes, Gamma factor and pole, and to positive semidefiniteness of its Gram matrices on a
two-prime Hecke orbit. Weak bounds self-improve (any eventual bound, any damped bound gives the sharp one),
so the needed input is qualitative, not a sharp constant. The obstruction is that every unconditional
source of positivity found here — the archimedean collar, finite Euler data, base Riemann–Roch — orients
only finite pieces. A proof must bring arithmetic information about infinitely many primes that is visible
on one orbit and fails on the golden curve.

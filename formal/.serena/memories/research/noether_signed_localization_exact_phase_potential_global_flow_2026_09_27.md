# Signed localization witnesses, exact phase potential, and global Noether flow

## Active goal / status
RH remains unproved and unfalsified. Goal remains active, completion only formal RH proof. This turn made verified progress (six new green leaves); no blocker. Continue conjecture/proof/fail/pivot toward actual arithmetic positivity. User rules: no sorry/new axioms/assumed missing theorem; no numerical computations; one own foreground Lean build at a time; final leaf audits `lake --old env lean` with oleans; wire umbrellas but never build whole umbrella; clean scratch; no heartbeat changes; no commit/push. Other chats edit/index concurrently: preserve their files.
Repo `/Users/michael/Documents/code/hgt/formal`.
Previous context `mem:research/noether_exact_arithmetic_localization_and_coercive_pieces_2026_09_27`, `mem:research/noether_full_weil_modulus_obstruction_2026_09_27`.

## Result and interpretation
Conjecture tested: maybe exact signed localization error always favors combining local positive pieces. FALSE in actual source space. Constructed same compact angle theta and actual u,v with v=|u| pointwise, cos(theta)u=v, cos(theta)v=u, sin(theta)u=sin(theta)v=0. Prime errors both exactly zero; continuous errors nonzero and opposite. No negative full Weil quadratic is shown.
Stronger positive finding: continuously scaling that angle gives literal two-channel arithmetic energy
`E(t)=Q(cos(t theta/pi)u)+Q(sin(t theta/pi)u)=Q(u)+B*(1-cos t)`, B>0, all prime errors zero. It is a sum of two actual source quadratics; no identification with one complex-modulated source was proved here (would require the real mixed-form imaginary part bridge).
The potential is exact, not an arbitrary kernel model. Constructed a mechanical Lagrangian with this potential, time-translation symmetry, Noether charge, Hamilton–Jacobi action, and global Newton flow on a chosen positive-speed energy curve. This is one inverse-Noether construction (kinetic term chosen), not a physical claim or canonical unique dynamics.
Missing RH issue: baseline Q(u) and arbitrary inter-source couplings remain uncontrolled. Pendulum conservation does not imply positivity of Q.
All continuous local potentials cancel from the localization defect and relative phase energy, so local multiplication corrections cannot remove this phase interaction.

## Six new audited leaves, namespace RHTower
All final individual audits exited 0 without warnings using `lake --old env lean Leaf.lean -o .lake/build/lib/lean/...olean`. All fresh oleans. Umbrella RHTower.lean lines 19724–19729 at audit time, MainTheorems imports RHTower.

### CCMThetaSeparatedAngle.lean (99 lines)
Imports exact arithmetic localization, modulus obstruction, Mathlib.Geometry.Manifold.PartitionOfUnity.
- `disjoint_tsupport_of_positive_gap`: a positive uniform gap between function supports persists in closures, by two closure_minimal arguments.
- `exists_schwartz_separating_angle`: closed s, compact t, disjoint -> compact real Schwartz theta zero on s, equal any prescribed phase on t. Uses compact thickening + smooth Urysohn + toSchwartzMap; no separator is assumed at arithmetic endpoints.
- `exists_separated_thetaArithmetic_phase_pair`: upgrades existing positive atom-free cross-pair phi,psi to disjoint tsupports and existence of separators for every phase. Outputs compact support, nonnegativity, ordered support gap, avoidance of every log n (n>=2), positive `thetaGammaPolarGroundCrossPairing`, and compact angle.

### CCMThetaSignedLocalizationWitness.lean (180 lines)
- `ccmSmoothSourceQuadratic_eq_zero_of_pointwise` utility via zero ground profile.
- `ccmThetaPrimeLocalizationError_eq_zero_of_separated_components`: generic source supported in ordered components phi/psi, no prime log links, theta constant 0/phase on components -> actual prime error=0. Proves density zero pointwise; no convergence assumptions.
- `exists_ccmTheta_localization_error_both_signs` (line86):
  exists aperture a, actual u,v, real Schwartz theta with:
  compact theta; v(x)=norm(u(x)) as complex;
  theta(x) in {0,pi} on support u;
  cosLocalized u=v, cosLocalized v=u;
  both sinLocalized pointwise zero;
  both prime errors=0;
  ErrContinuous(u)<0<ErrContinuous(v);
  ErrContinuous(u)=-ErrContinuous(v).
  Construction u=k*(phi-psi), v=k*(phi+psi), using old actual positive continuous cross pairing C. Full quadratic difference Q(v)-Q(u)=4C>0. Exact localization gives ErrC(u)=-4C, ErrC(v)=4C. All aperture/domain obligations proved.

### CCMThetaArithmeticPhaseOrbit.lean (126 lines)
- `ccmScaledPhaseAngle theta t=(t/pi)*theta` as Schwartz.
- `ccmPhaseLocalizationEnergy u theta t` = Q(cosLocalized scaledAngle)+Q(sinLocalized scaledAngle).
- `thetaLocalizationWeight_scaledPhase`: if theta at both points is 0/pi, W_scaled=((1-cos t)/2)*W_original.
- `ccmThetaLocalizationCross_scaledPhase`: same identity on actual physical correlation; points outside source support vanish.
- Both `ccmThetaPrimeLocalizationError_scaledPhase`, `ccmThetaContinuousLocalizationError_scaledPhase` exact integral scaling.
- `ccmPhaseLocalizationEnergy_eq`: for a 0/pi source angle,
  E(t)=Q(u)+((ErrPrime(u,theta)-ErrContinuous(u,theta))/2)*(1-cos t).
- `hasDerivAt_ccmPhaseLocalizationEnergy`: derivative coefficient*sin t.
- `exists_ccmArithmetic_positive_phase_potential` (line107): unconditional actual a,u,theta,B>0, compact theta, source angle 0/pi, ALL scaled prime errors zero, exact E(t)=Q(u)+B(1-cos t), derivative B sin t for every real t. Here B=2C in witness construction.

### CCMArithmeticPhaseAction.lean (199 lines)
For ANY real B, no positivity premise:
- `arithmeticPhasePotential B q=B*(1-cos q)`.
- `arithmeticPhaseEnergyLevel B=2*abs(B)+1`.
- `arithmeticPhaseSpeed B q=sqrt(2*(energyLevel-potential))`, strictly positive.
- `arithmeticPhaseSpeedBound B=sqrt(8*abs B+2)` positive and global upper bound.
- Potential abs<=2absB, exact derivatives for potential and speed.
- Lagrangian `v²/2-potential`; mechanical energy `v²/2+potential`.
- `arithmeticPhase_noether_charge`: v*dL/dv-L=mechanical energy.
- `arithmeticPhaseAction` literal time integral of L(q,q').
- `arithmeticPhaseAction_time_translation`: translating q and both time endpoints preserves action exactly.
- `arithmeticPhaseHamiltonJacobiAction`=integral speed; derivative speed and exact energy level.
- `arithmeticPhaseTravelTime`=integral reciprocal speed. Smooth/continuous, strict mono, drift bounded below by q/speedBound, tends +infinity/-infinity, hence onto. No ODE existence hypothesis supplied.

### CCMArithmeticPhaseFlow.lean (130 lines)
- `arithmeticPhaseTravelIso`, inverse `arithmeticPhaseTrajectory B t`.
- Proved derivative speed; second derivative=-B*sin q; exact mechanical energy=energyLevel.
- `arithmeticPhaseTrajectory_euler_lagrange` proved for constructed trajectory.
- `arithmeticPhaseFlow B q t=trajectory(B,t+travelTime(B,q))`.
- Flow zero and additive group law, derivative speed, conserved energy.
- Scope: flow on ONE positive-speed energy curve for each B, parameterized by initial position. Not arbitrary initial velocity / all phase-space energies.
- `exists_ccmArithmetic_phase_noether_flow` (line109) unconditionally connects actual arithmetic source phase potential to this flow:
  E(q)=Q(u)+potential(B,q), B>0;
  for all starting positions q and times t,
  `(d/dt flow)^2/2+E(flow)=Q(u)+2B+1`;
  trajectory q''=-E'(q).

### CCMThetaPhaseLocalPotential.lean (88 lines)
- `ccmSmoothLocalPotentialEnergy_localization`: V energies of cos/sin localized pieces sum to V energy of u, every continuous real V and complex smooth source.
- `ccmLocalPotentialLocalizationDefect`: total localized (Q+V) minus original (Q+V).
- `ccmLocalPotentialLocalizationDefect_eq`: exactly ErrPrime-ErrContinuous, independent of V.
- `exists_ccmLocalization_opposite_signs_all_local_potentials`: same compact pair/angle gives positive defect for u and negative for v for EVERY continuous V.
- `ccmPhaseLocalizationEnergyWithPotential`: phase sum with both local potential terms.
- exact equality E_V(t)=E(t)+V(u).
- `exists_ccmArithmetic_phase_potential_independent_of_local_potentials` (line76): actual B>0 family obeys E_V(t)-E_V(0)=B(1-cos t) for all V,t.

## Validation and state
- Six green leaf audits, fresh oleans; no warnings or heartbeat hacks.
- Thirteen `#print axioms` endpoint checks all only propext, Classical.choice, Quot.sound.
- Scratch `work/noether_arithmetic_phase_axioms.lean` deleted; absence checked.
- Whitespace/diff checks clean. Six umbrella imports present once. No umbrella/full build.
- Index refreshed successfully. First lint raced with other chats and found generated staleness; refreshed again (2 changed). Final lint has NO generated staleness and NO own unwired modules.
- Remaining unrelated unwired modules: MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, XiCriticalFloorBudgetSeparation, ZetaZeroDensityPowerSaving. Do not wire others' unfinished work.
- No own live process remains. No commits/pushes.

## Next meaningful mathematical directions (NOT proved yet)
1. Quantify why atom-free separated bumps do not immediately refute RH: continuous positive coupling grows ~exp(gap/2), but avoiding every log n near a large gap forces interval widths ~exp(-gap). Thus cross coupling for L2-normalized narrow bumps may decay while local Gamma diagonal grows. Need exact bounds on atom-free interval width and actual diagonal energy (coarse aperture envelope is far too large). This could establish a broad disconnected two-bump positivity range instead of another generic obstruction. This is a conjectural direction; no asymptotic or positivity theorem added for it.
2. Strengthen the witness construction to arbitrarily narrow nonzero positive subbumps, retaining atom-free positive cross and enforcing existing explicit total-support coercivity. Would certify that both error signs coexist with actual positive full energies; currently Q(u) sign unknown in exported witness.
3. Multi-component phase energy might expose arithmetic cancellations missed by universal error signs. Avoid re-proving generic Schur/finite-Gram criteria already extensive in corpus.
4. A one-complex-source phase-orbit bridge from our two-real-channel sum could reuse real mixed-form imaginary-part-zero lemmas; not yet proved here.

## Lean repairs
- `HasCompactSupport.const_mul` absent. Bind `htc : HasCompactSupport (fun x:R=>phase*f x) := hfc.comp_left (g:=fun z:R=>phase*z) (mul_zero phase)`.
- ContDiff proof use `contDiff_const.mul hfd`; `.const_mul` field not available in this imported context.
- Deprecated SchwartzMap.zero_apply -> zero_apply.
- `integral_eq_zero_of_ae` target may retain `0 p`; simp Pi.zero_apply explicitly.
- `abs_of_pos (thetaCuspTiltSource.pos x)` may not rw k after unfolding; specify `(show 0<thetaCuspFullSource x from thetaCuspTiltSource.pos x)`.
- Derivative proofs for named real defs sometimes fail simpa with different module instances. `convert!` matching the derivative theorem using1 then simp/ring resolved without heartbeat changes.
- Support disjointness closure via closure_minimal and isClosed_le handles uniform positive gaps cleanly.

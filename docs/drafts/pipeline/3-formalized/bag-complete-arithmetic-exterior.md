# BAG: complete arithmetic exterior and original sharp near-cone reduction

- **ID:** bag-complete-arithmetic-exterior-30az
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** P1:bag-global-conormal-localization; ChiCubicExteriorSource; ChiCubicNearConeReduction.
- **Statement:** The COMPLETE projected arithmetic exterior of the literal selected cubic has every polynomial decay order, uniformly in all prime sets and projector moduli; the ORIGINAL sharp cubic differs negligibly from its ENTIRE shrinking near-cone action.

## Exact new knowledge

For H=N^(1/4), epsilon=N^(-1/8), let A_N be the original controlled physical
Schwartz amplitude, D(xi)=xi_2+xi_0*xi_1, and
B_N=FourierInv((1-chi(D/epsilon))*Fourier(A_N)). Then for EVERY natural a
there is C_a>0 such that for EVERY admissible N, EVERY finite prime-source
set P and EVERY positive projector modulus D0,

    norm(bagCriticalDefectAction P D0 B_N) <= C_a/N^a.

Admissibility includes ALL sufficiently large original natural N. The
entire critical rational source, all integer lifts, all congruence aliases,
and BOTH projectors are present. Constants incur no absolute atom-mass
cost. No analytic premise, omitted signed sheet, finite-frequency
truncation or new axiom is used.

The retained physical test A_N-B_N has exact Fourier transform
chi(D/epsilon)*Fourier(A_N). With the actual source set through2N and
actual modulus floor(2N)+1, exact source linearity gives

    smoothed original cubic = near-cone action + complete exterior action.

The same controlled cutoff already has negligible sharp/smooth error.
Consequently, on the FULL original natural scale,

    log²N/N * norm(original sharp cubic - bagCubicNearConeAction N) -> 0.

This closes the full exterior arithmetic sector and its original-source
attachment. It does not prove cancellation of the retained tube, the
original cubic, growing mixed moments/cofactors or common-height BAG
return. RH remains open. Next hard target: P1:bag-entire-near-cone-arithmetic.

## Dependency-closed proof

1. Actual Schwartz decay supplies a summable product-lattice majorant
   uniform on every bounded translation region. Normal periodization is
   continuous. Integrating the entire periodization over the fundamental
   cube is justified by the sum of integral norms. Twisting by a unit
   character preserves that majorant; every torus coefficient is the
   exact shifted physical Fourier coefficient. Torus Fourier inversion
   gives full3D Poisson for ANY Schwartz input and ANY real shift.
2. Product-coordinate pullback is continuous on Schwartz spaces. Full
   Poisson identifies the complete lifted Fourier test with the periodic
   physical lattice series, without a compact-support premise.
3. The existing complete critical-source bound retains both projector
   masks and bounds the source by the weighted lattice norm. Summing the
   proved reciprocal-square product majorant controls this by one fixed
   Schwartz seminorm rectangle. Continuous pullback gives ONE finite
   physical seminorm family, independently of P and D0.
4. The actual exterior has arbitrary-power decay in EVERY physical
   seminorm, with the normal derivative order chosen after the finite
   recipient family and requested decay order. Taking its finite supremum
   in step3 proves the entire arithmetic exterior estimate.
5. Absolute Schwartz periodization proves source subtraction exactly.
   On the actual natural scale, the original smoothed-source identity
   therefore splits into the entire near action and entire exterior.
6. Exterior order0 already gives normalized vanishing since log²N/N->0.
   Combining with the existing SAME-cutoff sharp/smooth error via the
   norm triangle inequality proves the stated original sharp reduction.

## Lean certificate

- ChiCompactLatticePoisson: poisson_of_summable_translates (all analytic
  inputs are produced by the Schwartz consumer; old compact theorem retained).
- ChiCubicSchwartzPoisson: full_schwartz_poisson.
- ChiRamanujanThreeFrequencyLattice: ramanujanTripleSchwartz_weighted_sum_le.
- ChiCubicExteriorSource: bagLiftedFourierTest_eq_periodic,
  bagCriticalDefectAction_uniform_seminorm,
  bagCubicShrinkingExterior_source_rapid_decay.
- ChiCubicNearConeReduction: bagCubicNearConePhysical_fourier,
  bagCubicCompleteExteriorAction_rapid_decay,
  bagCubicCompleteExteriorAction_negligible,
  primeGaussianCubicSmoothedOffDiagonal_nearCone_split,
  primeGaussianCubic_nearCone_reduction.

## Audits

All final checks used lake --old env lean <leaf> -o <own olean>, one
foreground process at a time. No umbrella or full build. Direct audits
66849/51816/3866/10040/5368 passed. One constructor-name collision with
the previous cone branch was corrected: ONLY the new N>=exp1 constructor
became bagCubicExpControlledPhysicalSchwartz. Five-leaf dependency-order
reaudit12356 passed. Old N>1 constructor and its consumers are unchanged.
Combined-import scratch85390 and final axiom85038 passed with both branches;
a direct equality probe confirms both constructors give the same function
on the overlapping domain.

Axiom audit85038 covered all25 new/touched public theorem endpoints:
only propext, Classical.choice, Quot.sound. No sorryAx or added axiom.
All three new umbrella imports occur exactly once. Index87063 passed
(5 changed,0 removed). Authoritative lint72188 reports ZERO findings in
the nine touched leaves; repository-wide exit1 retains24 unrelated
unreachable modules and367 size warnings. Scoped whitespace check passed.
Owned scratch sources were cleaned after terminal audits; logs/search JSON
are retained under /tmp with30az suffix. No commits, full builds,
subagents, computations or heartbeat overrides.

## Gates

- [x] Complete unconditional sector target specified.
- [x] Dependency-closed paper proof and all source exchanges.
- [x] Direct leaf, combined import, axioms, unique umbrella wiring;
  own lint findings zero, unrelated repository lint failures disclosed.
- [ ] Publication-ready standalone paper.

## Log

- 2026-10-06,30az: full Schwartz Poisson and complete arithmetic source
  attachment succeeded. Source-only SpherePacking Poisson with a sorry
  body was rejected and never imported. Original sharp near-cone
  reduction also closed. Continue with the entire retained arithmetic tube.

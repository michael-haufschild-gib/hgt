# Cycle26 — bounded-energy closure at the fixed negative Fejer source

Status: OPEN diagnostic; SURVIVES PRELIMINARY ATTACK. No paper theorem,
Lean theorem, novelty claim or WP02 lower bound is asserted. The selected
claim below is E-escape. Its opposite remains a serious competing possibility.

## Exact competing claims

Use the literal `RHTower.fejerTest` from
`WeilPositivitySummableWeightsObstruction.lean`: the nonnegative flat bump
with parameters 17/50 and 17/1000, not the differently named spectral Fejer
test in WeilDeviationFejerTest. Set

    rho_psi(t) = |paperFT(fejerTest)(t)|^2.

Let C range over every finite family of actual complex compact C2 polar
tests f_i, with arbitrary apertures a_i, coefficients alpha_i>=0, and

    sum_i alpha_i atomCoeff(f_i,n) = 0  for EVERY integer n>=2.

No common profile, common lattice, bound on row count, aperture bound,
derivative bound, or energy sign is part of this class. Define

    rho_C(t) = sum_i alpha_i |paperFT(f_i)(t)|^2,
    d(C) = integral |rho_C-rho_psi|,
    E(C) = sum_i alpha_i archEnergy(f_i).

Each integral exists by the actual compact C2 source theorems. There is no
mass-one normalization: d(C)->0 already forces convergence to the fixed
positive Fourier mass of psi.

**E-escape:** for every real B, there exists epsilon>0 such that every C
with d(C)<epsilon has E(C)>B.

**E-recovery:** there exists a real B such that for every epsilon>0 there
is a C with d(C)<epsilon and E(C)<=B.

These are exact logical negations. E-escape is equivalently: every actual
recovery sequence with d(C_k)->0 has E(C_k)->+infinity. That statement may
hold because no recovery sequence exists; existence must be investigated
separately rather than assumed. Failure of E-escape supplies a bounded-cost
sequence by choosing epsilon=1/(k+1). No abstract probability measures may
replace the actual finite source families in E-recovery.

[OPEN CORE] Prove the uniform separation of every archimedean-energy
sublevel from rho_psi, or construct actual exact-null polar recovery families
with a bounded signed energy cost. The fixed-profile theorems do neither.

## Why this tests a different obstruction

The actual psi has negative archimedean energy and all its integer samples
vanish, since its autocorrelation is supported in |y|<=17/25<log 2.
It is not polar. Its two exponential moments are strictly positive because
the source is nonnegative and positive on an interval.

The corpus's farPolarTest X has both polar zeros and Fourier density

    rho_psi(t) * (1-sech(X/2)*cos(X*t))^2.

Therefore its L1 distance from rho_psi is at most
(2*sech(X/2)+sech(X/2)^2)*integral rho_psi, tending to zero. Its energy
approaches the negative seed energy. It fails exact integer nullness.
Thus neither polar cancellation by itself nor approximate coordinatewise
integer blindness gives E-escape. The simultaneous exact constraints must
do the work.

If E-escape holds, negligible spectral-mass repairs of this fixed source
cannot retain bounded energy, even with arbitrary profiles and apertures.
If E-recovery holds, its literal recovery family and limiting energy defect
would identify a finite-cost escape mechanism omitted by fixed-profile
arguments. Bounded recovery energy does NOT imply negative energy or refute
RH. Likewise E-escape does NOT prove positivity for arbitrary null families,
and it does not handle the nonzero exposing ray.

## Hostile audit

1. **Common-profile mass identity.** ExposingRayLattice's exact recovered
   mass excludes nonzero null mixtures on its one Fejer lattice, spacing>=4.
   It is not a theorem about this unrestricted class.
2. **Coherent completion.** Existing geometric completion has bounded
   energy cost but a retained positive spectral correction. Its density
   identity does not show d(C)->0. Dropping that correction changes the task.
3. **WP01 fixed-profile escape.** JointEnergyEscape fixes the profile and
   prime; PacketEnergy uses disjoint narrow integer packets. Neither gives
   uniform control of all varying profiles in C. Reproving their bounds is
   REDISCOVERED, not a new route.
4. **Compactness.** The actual ground-state compact embedding fixes the
   aperture. No such bound occurs here. Polar exponential evaluations do
   not pass through real-frequency L1 convergence when apertures escape.
5. **Energy versus energy tightness.** A bounded logarithmic moment does
   not ensure uniform integrability of that moment. Small mass can carry
   nonvanishing energy at high frequency. This elementary fact supplies no
   actual source recovery family; conversely it blocks a naive limit proof.
6. **Zeta moment.** The proved matched_moment at t=0 fixes the zeta moment
   of every C to its Fourier mass. Its symbol is unbounded. Passing that
   moment to an L1 limit needs additional tail control, which has not been
   derived from the logarithmic energy bound. The earlier large-value
   obstruction forbids assuming a global O(log |t|) bound for Re zeta.
7. **No covert derivative bound.** Dense integer sampling at a remote lag
   does not imply an exponentially accurate interpolation error from a
   logarithmic energy bound. C2 regularity is individual, not uniform.

No counterexample or dependency-closed proof of E-escape was obtained.
An informal proposal that lost energy must equal the seed's full pole term
also has no proof; it is not part of the conjecture or an established law.

## Parent theories and novelty limits

Corpus queries and their complete candidate/source audits are recorded in
EVIDENCE.md. Direct sources checked include the actual far-polar formula,
fixed-lattice identity, geometric-completion density, WP01 packet/Joint
energy reports, and the fixed-aperture ground-state compactness proof.

[Burnol's invariant analysis](https://arxiv.org/abs/math/0101068) supplies
the conductor interpretation and a support-restricted positivity result.
[Connes--Consani](https://arxiv.org/abs/2006.13771) study the archimedean
Sonin trace and its correction. These abstracts were checked for scope;
neither is used as an imported proof of E-escape.
[Groskin's finite dictionary](https://arxiv.org/html/2607.02828) concerns
finite Galerkin forms and archimedean tail certification, not an unrestricted
bounded-cost recovery theorem. No computational claims from it are used.
External novelty remains unestablished; a search mismatch is not novelty.

[Suzuki's whole-line Hilbert-space article](https://doi.org/10.4153/S0008414X25101739),
abstract and introduction, explicitly uses RH for that Hilbert completion
and distinguishes it from Yoshida's unconditional finite-interval method.
It cannot supply the missing unconditional closure statement here.

## Next attack and scope control

First test whether variable-profile positive corrections can make their
total Fourier mass vanish while preserving every exact integer equation.
Retain their entire signed Gamma cost and the two actual poles. A concrete
recovery family would decide E-recovery; a uniform source inequality must
cover arbitrary row count and aperture to decide E-escape. Do not formalize
the logical dichotomy, fixed-aperture compactness, or another conditional
receiver as new frontier progress.

This is a diagnostic for the t=0 obstruction. The primary WP02 producer
remains VANISHING-MASS-DEFECT-CONJECTURE.md. No reduction from this diagnostic
to that all-family, nonzero-ray estimate has been proved.

## Cycle27 update: separate recovery existence from energy cost

`POLAR-FIBRE-DENSITY-PROOF.md` now gives a dependency-closed paper argument
for actual spectral L1 recovery in every fixed finite integer-atom fibre,
including this literal Fejer null fibre. Cycles27–29 formalize the complete
argument in `WeilWorkExposingRayFibreTransfer.lean`,
`WeilWorkExposingRaySeparatorExtension.lean`, and
`WeilWorkExposingRayFibreDensity.lean`. The final leaf's actual theorem
`exists_fejer_null_recovery` preserves every raw integer atom exactly and
passes its saved-source audit. Thus E-escape cannot hold vacuously through
nonexistence of recovery. This gives no energy bound and decides neither
E-escape nor E-recovery. Both remain OPEN. The new sublogarithmic weighted
candidate is in `SUBLOG-FIBRE-CONJECTURE.md`; no weighted recovery is proved.

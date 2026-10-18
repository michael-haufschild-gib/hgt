Companion to `mem:bvi_dilation_successor_corpus_reuse_2026_10_18`.
Workspace /Users/michael/Documents/code/hgt. PAUSED BY USER on 2026-10-18.
User cleared the active goal, then requested finishing started Lean work, wiring,
and docs before pausing. Closeout complete; no active goal. Resume only on request.
Research objective: actual additive Bezout jump geometry inside high-scale dilation profiles.
No hgtl7, no RH work, no numerical experiments, no full builds, one owned Lean at a time.
User specifically insists on the Lean corpus research command, not rg alone.

C12-C13 completed 2026-10-18:
- formal/GaloisForLFunctions/BezoutValuationIncidence/DilationClockRelativeGapAndSignedComplement.lean
  187 lines, 4 concrete definitions + 4 public theorems.
- formal/GaloisForLFunctions/BezoutValuationIncidence/DilationClockComplementPrimeSurvival.lean
  221 lines, 2 public theorems.
Both wired once into BezoutValuationIncidence.lean, narrow README entries added.
No umbrella built.

C12 uses existing leastSuccessorSeed_spec, totient-square amplitude bound,
and exact clock-sector/profile seed estimates. For pa=qb+1, a>=1, the geometry
forces q-1 <= |p-q| a when p<q or q+1<p. Reverse consecutive p=q+1 is excluded
essentially. Thus |seed_s(p,q)| <= phi(s)^2 |p-q|/(q-1).
Set s=primeRadical r, v=lagVisibilityClock r, H=v*(p*q*s+1)-1.
New concrete definitions:
ramanujanClockSuccessorHorizon, ramanujanClockSuccessorSector (sqrt(pq)*S_r(v,H)),
ramanujanClockSignedComplement (sqrt(pq)*(full finite realized-gap sum-S_r(v,H))),
ramanujanClockSuccessorRelativeGapBudget
 = v*sqrt(q)/sqrt(p)*phi(s)^2*|p-q|/(q-1) + v*s*phi(s)^2/sqrt(pq).
The isolated sector is bounded by this budget. The original Phi minus its
literal signed complement is bounded by the same budget plus the physical
cutoff error sqrt(pq)*PrimitiveBound(r)^2/(H+1).
Data-only capstone dilation_clock_relative_gap_and_signed_complement(r,n,d)
uses R=r+2, p=n+2, q=p+d+1.

C13 clock_successor_total_error_le_relative_gap bounds cutoff+budget for
2<=p<q<=2p by
  2*v*phi(s)^2*(q-p)/p + (PrimitiveBound(r)^2+v*s*phi(s)^2)/p.
Data-only exists_prime_clock_complement_near_diagonal(r,N,k), line116:
R=r+2, G=Gram(R,R)>0. There are primes N<p<q, q<(1+1/(k+1))*p,
|clock sector|<G/(k+2), |signed complement-G|<G/(k+2), and complement>G/2.
Reuses actual-profile continuity/diagonal identity and exists_prime_pair_ratio_lt.
This is a cofinal-family positive survivor, not a uniform signed prime-packet bound.

Audit evidence:
logs/bvi-clock-relative-gap-original.txt exit0, no diagnostics.
logs/bvi-clock-prime-complement-original.txt exit0, no diagnostics.
logs/bvi-clock-relative-gap-prime-complement-axioms.txt exit0:
all ten public declarations exactly [propext, Classical.choice, Quot.sound].
Replay /tmp/bvi-c12-c13-axioms.lean. Merged C12/C13 draft Lean files removed.
Index log logs/bvi-clock-relative-gap-prime-complement-index.txt exit0.
Exact quoted discovery /tmp/bvi-c12-c13-discoverability.json returns both capstones.
All scoped whitespace/forbidden-token/import uniqueness checks passed.
No owned process remains at checkpoint.
C1-C13: 111 public declarations in12 modules, plus C8's separately exported
existing gcd-divisor formula.

Final authoritative lint still fails:
logs/bvi-dilation-pause-closeout-lint.txt exit1, 381 size warnings.
One unrelated error: research leaf module at package root:
TransHorizonIncidenceMechanics.lean; move it into an owned theorem area.
The earlier unreachable ArithmeticPositivityTheory-module error is absent from
this run. No active forbidden-declaration error. Do not edit unrelated owners'
modules or claim global lint passed.

Current frontier corrections from fresh corpus:
- Collective prefix estimates and all-level local centering already exist.
- SharedBirthPronicCellCovariance.sharedBirthUnitGapCovariance_coherent:
explicit distinct ordered gaps have positive mixed-level covariance equal
to a diagonal variance. Local centering does not imply global nonpositivity.
- PronicResidueGapEnergyAndPrimePairDistance already proves exact pre-overlap
residue prefix and h*harmonic(floor(p/h))-h <= residueGapPronicEnergy(p,p+h),
plus harmonic upper bounds. All25 lexical hits were inspected, including page2.
- RamanujanDilationProfileResidueGapBudget has actual scaled-distance HasSum
and actual-profile upper bound via Mobius-weighted residues. Residue lower
bounds cannot be reversed through that Cauchy-Schwarz argument.

C14 (paused paper candidate; no dedicated Lean module or period-cell proof started):
r>1, q=p+h, k=r*t>0, k*h<=p. On n in Ico(k*p,k*q), quotients equal k and k-1.
Existing periodicity plus coefficient-at-divisible-lag gives A_r(k)=0 and
A_r(k-1)=-phi(r). Hence actual scaled primitive difference equals q*phi(r).
Its exact pronic square mass on this cell is h*q*phi(r)^2/(p*k).
These cells are disjoint for1<=t<=K=floor(p/(r*h)), yielding proposed lower bound
  h*q*phi(r)^2/(p*r)*harmonic(K)
  <= (p+q)*G(r,r)-2*sqrt(p)*sqrt(q)*Phi_r(p/q).
First formalise literal cell identity, then disjointness and transfer using
existing hasSum_scaled_pmRamanujanPrimitive_distance.
No cusp/derivative claim yet.

Exact existing reuse interfaces:
- RHTower.pmRamanujanPrimitive_periodic hr N: A_r(N+r)=A_r(N).
- RHTower.pmRamanujanPrimitive_period_sum hr: A_r(r)=0.
- RHTower.pmRamanujanPrimitive_succ r N: A_r(N+1)=A_r(N)+c_r(N+1).
These sources read in RHTower/PMPowerDampedMobiusRamanujanPrimitive.lean.
- ramanujanNaturalCoefficient_re_eq_lagCoefficient, DilationJumpValuationClock.lean:22.
- ramanujanLagCoefficient_of_dvd {q h}(q|h): lag coefficient=totient,
  NonMarkovianLagOperatorAlgebraAndPrimePowerRevival.lean:60.
Do not write a new character-sum proof for multiples.
- Nat.div_eq_of_lt_le hl hu supplies exact quotient cells. Existing private
gap_residue_first_cell in PronicResidueGapEnergyAndPrimePairDistance.lean
contains reusable boundary proof.
- Public sum_Ico_reciprocal_pronic in that module:42 now exports the existing
private gap_pronic_interval proof: for 0<a<=b, sum over Ico a b of
1/(n*(n+1)) equals 1/a-1/b. Reuse this interface; do not copy its proof.

C14 research JSONs:
 /tmp/bvi-c14-profile-cusp-prior-research.json
 /tmp/bvi-c14-actual-primitive-lower-research.json
 /tmp/bvi-c14-coefficient-totient-research.json
Each20 candidate +20 source statements inspected; partial=false but semantic
coverage unmeasured, refresh background, mostly source-only and some stale coverage.
Irrelevant proposed ingredient sets were rejected. Absence is not novelty evidence.
 /tmp/bvi-c14-residue-gap-lower-research.json and -page2.json (all25 hits).
 /tmp/bvi-c14-primitive-period-api-research.json (all11 hits).
 /tmp/bvi-c14-real-lag-api-research.json and /tmp/bvi-c14-lag-totient-api-research.json.
Exhaustive rg found14 literal-profile source files; all16 profile-bearing
declaration statements in the four older cross-depth/cofactor/two-prime/hypercube
interfaces checked. They do not replace the proposed actual-cell lower bound.

Main tracking card:
docs/drafts/pipeline/1-in-progress/bvi-dilation-successor-jump-coupling-2026-10-18.md.

User-requested pause closeout:
Only additional Lean change after C12/C13 was the six-line public interval
wrapper above; underlying private proof unchanged. Original-source audit
logs/bvi-period-jump-interval-interface-original.txt exit0, no diagnostics.
Scratch audit /tmp/bvi-period-jump-interval-interface-axioms.lean exited0;
logs/bvi-period-jump-interval-interface-axioms.txt reports exactly
[propext, Classical.choice, Quot.sound]. Existing owning module imported once.
README and tracking-card status updated. Scoped git diff --check passed.
Index logs/bvi-dilation-pause-closeout-index.txt exit0 regenerated API/gaps/overview.
Exact corpus query /tmp/bvi-pause-closeout-interval-discovery.json returned one
hit, the public wrapper at its canonical path:42; inspected. Earlier narrow
/tmp/bvi-c14-reciprocal-interval-research.json returned17 existing jump-kernel
hits, all inspected. Retrieval does not certify compilation or semantic coverage.
All owned Lean, search, lint, and index processes have terminated. No full build,
numerical experiment, heartbeat increase, commit, or push. Work paused.

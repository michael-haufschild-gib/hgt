# SZ: every Xi-identifying admissible shift approaches the relative spectral floor

- **ID:** SZ-SHIFT-EDGE
- **Stage:** 3-formalized
- **Type:** PROVED necessary condition; not an RH proof
- **Source:** actual prescribed profile; SZ-RAISED-SHIFT; actual interval Friedrichs operator.

## Exact result

Let C_a be the actual interval covariance, c_a its prescribed metric shift,
and E_a=1/norm(C_a)-c_a its actual attained ground energy. Parameterize
every strictly admissible shift by

    m>0, d=c+(m-1)/norm(C).

Lean proves this parameterization has range exactly (-E,infinity), and

    (E+d)/(E+c)=m.

The source response is constructed, without an inverse premise, as

    x=C*(I+(m-1)C/norm(C))^(-1)*p, where p(u)=exp(u).

For any cofinal aperture schedule, a nonzero limit of its literal Fourier
carrier at even one imaginary point i*s, 1/2<s<1, forces m->0. In particular,
local uniform identification with the normalized Xi target on the upper
half-plane forces

    (E_a+d_a)/(E_a+c_a) -> 0.

The source is the fixed exponential source already used by actual V2.
No assumption on simplicity, parity, source overlap, bounded shift,
regularity of the schedule, or sign of d is used. This does not construct
an Xi-identifying schedule and does not prove RH. It is relative approach
to the floor, not an absolute energy-gap limit.

## Dependency-closed paper proof

Put mu=norm(C)>0, q=min(1,m), and T=I+(m-1)C/mu. Positivity of C and its
operator-norm bound give T>=qI. Thus T is invertible on the actual interval
space. Its constructed inverse gives the actual equation (A+d)x=p.
The exact transfer identity

    T*(d*x-p)=c*C*p-p

gives q*norm(d*x-p)<=norm(c*C*p-p). Transport through the actual physical
isometry, Cauchy--Schwarz, c<=K*exp(a), and the previously audited source
profile show that both margin-weighted complex mixed errors tend to zero
on the joint filter a->infinity with arbitrary m>0.

Write P=d*exp(-(1+s)a)*<p_s,x> and M=d*exp(-(1+s)a)*<p_-s,x>.
The actual free Gram limits give

    q*(P-1/(1+s))->0, q*M->0.

If the literal carrier B tends to L!=0, its unscaled denominator is
eventually nonzero. The exact quotient identity then gives

    q*P = Cayley(is)*(q*M)/B -> 0.

This does not divide by d; d=0 is allowed. Subtracting the weighted
denominator error gives q/(1+s)->0, hence q->0. Eventually q<1 and q=m,
so m->0. The unconditional nonzero first Xi defect supplies an imaginary
point on the segment where the Xi target is nonzero.

## Lean and audit ledger

- `SuzukiSpectralMarginSource.lean`: 9 public theorems; exact floor
  coordinate/range, constructed inverse, actual source equation and
  weighted defect. Scratch56723 and final17124 exit0, warning-free.
- `SuzukiSpectralMarginLimit.lean`: 3 public theorems; physical defect and
  full complex weighted source limits. Scratch40762 and final44729 exit0,
  warning-free. Explicit source vectors resolve inner-product inference.
- `SuzukiSpectralMarginNecessity.lean`: 3 public theorems; literal imaginary
  quotient, arbitrary nonzero-limit necessity, Xi relative-floor necessity.
  Scratch15326 and final15580 exit0, warning-free. Removed a redundant
  tactic after `field_simp` closed the quotient identity.
- `SuzukiRaisedMetricShiftCarrier.lean`: existing nonzero Xi segment witness
  exposed publicly for reuse; final2368 exit0, warning-free.
- All three new imports wired once in `GaloisForLFunctions.RHTower`.
- Axiom audit39186 for all15 new public theorems plus the reused witness:
  exit0; every theorem uses only propext, Classical.choice and Quot.sound.
- Lint63539 exited1 with10 unrelated unreachable modules:
  CCMApertureChainProfile, CCMApertureTranslationChains,
  CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
  CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
  MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
  ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
  None of the current leaves is listed. Global lint is not green.

Final commands, from `formal/`, for each of the four leaves above:

    lake --old env lean GaloisForLFunctions/RHTower/<Leaf>.lean \
      -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Leaf>.olean

No full or umbrella build, numerical experiment, heartbeat increase,
subagent, commit or push. A brief accidental overlapping scratch check was
terminated by its owned PID (replacement77328 exit143); see working log.

## Corpus provenance and next hard problem

Search1190824 was partial/pending with source-only candidates and no proof
ideas/ingredient sets. Direct source inspection and final Lean audits
establish applicability; search absence is not a novelty claim.

The previous simple-even-ground Cayley obstruction remains applicable only
when its actual leakage hypotheses are proved. Relative floor approach
does not provide those hypotheses or allow exchanging a fixed-aperture
ground-edge limit with aperture growth. The source-defect strengthening
is now proved in P3:sz-actual-source-defect-quasimode: amplification forces
the actual normalized defect to satisfy the top covariance eigen-equation
asymptotically in relative scale. Its signed parity behaviour, unshifted
canonical-head positivity, lawful identification and RH remain open. The
next direct sign target is P1:sz-canonical-head-joint-phase-credit.

Cleanup verified: all10 owned scratch/search/audit files removed; all owned
processes terminal. Audited leaf oleans retained. Targeted diff whitespace
check and new-file whitespace/import checks passed; each new import occurs
once. Unrelated working-tree changes preserved.

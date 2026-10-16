# EWU: critical logarithmic one-pole fibre recovery

Status: formalized. Targeted oleans built; seven direct leaf audits passed.

## Objective

Remove the strict beta < 1 restriction from exact whole-integer-fibre recovery
of finite positive one-pole source mixtures by two-pole source mixtures. Work
at the actual logarithmic spectral weight, without a new analytic premise.

## Corpus frontier

`WeilWorkExposingRayOnePoleFibreDensity` proves recovery only below beta = 1.
`WeilWorkExposingRayCriticalBoundary` gives the all-frequency Dirichlet ceiling.
`HolomorphicQuadraticBoundary` removes quadratic boundary defects from such a
ceiling. `EvenSectorAbelLaplace` gives exact window-sum Laplace factorization.

## Conjecture log

1. Extend cosh doubling directly using quadratic Abel cancellation. Rejected as
   a proof: sparse pointwise doubling does not itself control signed Laplace
   averages. Missing implication must not be assumed.
2. Use large translated differences of the one-pole source itself, rather than
   small differences of its primitive. Candidate proof below.
3. Lift the completion back to actual EWU witnesses: every positive full-source
   mixture should admit finite positive EVEN two-pole recovery in its exact
   arithmetic fibre with arbitrarily small excess of the actual archimedean
   plus pole cost. Paper proof: assume a strict cost gap; the algebraic fibre
   support lemma produces arithmetic weights positive on even polar tests.
   Automatic EWU completion makes these same weights positive on the original
   full mixture, contradicting the gap. Signed coordinate rays supply every
   fibre, including the entire zero tail. Apply support to positive mixtures
   as rows and flatten them, avoiding any spectral factorization premise.

## Dependency-closed paper proof

Let Q be an actual critical spectral-minus-arithmetic separator, nonnegative
on every compact two-pole source. Its coefficients b have absolute Dirichlet
convergence for Re z > 1/2. Write B(s) = sum b(n)n^(-1/2-s).
The all-frequency ceiling and the holomorphic Harnack theorem give s^2 B(s) -> 0.

For a compact source f killing +i/2, take
f_a = T_(-a) f - exp(-a/2) f; for f killing -i/2 take
f_a = T_a f - exp(-a/2) f. Both evaluations now vanish. Their spectral
densities converge in logarithmically weighted L1 to that of f.

Let q be the real even autocorrelation of f. Its bilateral Laplace transform
H(s) at 1/2+s has H(0)=0, because one of the two pole evaluations of f vanishes.
Compact support gives H(s)=s J(s), with J continuous at zero. The exact
window-sum Laplace identity then gives
s integral exp(-(1/2+s)a) [arithmetic translated kernel] da -> 0:
the noncompact piece is s B(s) H(s)=s^2 B(s) J(s); all cutoff and reverse-window
terms have bounded support and vanish after multiplication by s.
The spectral translated kernel is bounded, so its same Abel average vanishes.

The polar-source inequality is
(1+exp(-a)) Q(f) >= 2 exp(-a/2) K_f(a).
Average with s exp(-sa) over a>=0 and pass to zero. The left multiplier tends
to 1 and the right side to 0, proving Q(f)>=0 at the critical cost.

Strict L1 separation of an exact arithmetic fibre, using the existing signed
coordinate resonators and algebraic null-cone support theorem, then proves
the critical weighted closure equality and actual finite positive recovery.
Every integer sample, including the zero tail, is exact in each recovery.

## Audit obligations

- Verify every sign and normalization against actual Lean definitions.
- Derive absolute convergence and boundary cancellation from the separator.
- Prove H(0)=0 and differentiability; do not assume a Laurent expansion.
- Pay every integral interchange and half-line cutoff.
- Produce closure equality/recovery, not only a new bound or conditional limit.
- Targeted foreground builds, direct leaf audits, umbrella wiring, axiom audit,
  formal lint, cleanup. No numerical computations or heartbeat changes.

## Proof refinement during formalization

No integration of the full separator kernel is necessary. For a one-pole f,
the translated two-pole differences directly give K_f(a) <= K_f(0) cosh(a/2).
If K_f(0)<0, the bounded spectral part and compact support of the reverse
arithmetic window force the forward arithmetic window to dominate
c exp(a/2)-M on a tail, with c>0. Its cancelled Abel average rules this out.
This pays the missing critical implication without any pointwise Tauberian
assumption. The exact half-line head is uniformly bounded by an existing
compact-window lemma.

Every source, cutoff and fibre obligation above is now discharged in Lean.

## Formalized results

- `WeilWorkExposingRayCriticalCancellation.tendsto_critical_quadratic_zero`:
  actual critical separator supplies every analytic input to Harnack.
- `WeilWorkExposingRayCriticalWindowCancellation.tendsto_abel_window_zero`:
  exact compact-window cancellation, including the entire half-line cutoff.
- `WeilWorkExposingRayCriticalOnePole.critical_separator_onePole`:
  critical logarithmic extension on either one-pole source, without a new
  growth, lower-floor, Laurent, sign or recovery premise.
- `ExposingRayTransfer.OnePoleFibre.critical_fibre_closure_eq`:
  premise-free equality of one-pole and two-pole closures at beta = 1 in every
  exact whole-integer fibre. The existing finite positive raw recovery theorem
  now covers the closed exponent range 0 <= beta <= 1.
- `EvenSector.exists_evenPolar_exact_fibre_recovery`: actual finite positive
  EVEN pole-free mixtures preserve the complete integer trace of any positive
  full-source mixture, with arbitrarily small excess of its actual pole-plus-
  archimedean cost. No positivity premise on the Weil functional is used.
- `EvenSector.evenPolar_energy_fibre_closure_eq`: premise-free equality of the
  closed actual-energy epigraphs in every arithmetic fibre. This is the direct
  EWU witness-level consequence; it supplies witnesses, not a receiver.

## Scope and remaining obstruction

The critical weighted spectral recovery rows need not be even. The separate
EWU recovery rows ARE even and pole-free, preserve the entire arithmetic trace,
and recover the actual energy epigraph; no full spectral-norm recovery of those
even rows is claimed. These are different, explicitly stated conclusions.

Neither theorem proves that blind-fibre energies are nonnegative. Thus cone
nonemptiness, the global exposing-ray lower inequality and RH remain open.
Unrestricted full-source recovery at critical spectral cost is not claimed.

## Validation

- Foreground targeted `lake --old build` produced all four new oleans and
  rebuilt the three changed leaves. No full or umbrella build was run.
- Final `lake env lean <file>` audits passed for all seven changed/new leaves,
  with empty logs and no warnings.
- Eight `#print axioms` checks used a temporary file: only `propext`,
  `Classical.choice`, `Quot.sound`. Both closure capstones have no premises.
- New modules wired into `RHTower.lean`; generated Lean index refreshed.
- No proof debt, computations, new axioms, or heartbeat changes in this work.
- Global formal lint reported only unrelated concurrent umbrella omissions:
  `CHMDPolarJumpForm`, `CHMDPolarTransfer`, `DeningerMeyerConvolutionTopology`,
  `PaperThetaConvolutionGauge`. None belongs to this contribution.

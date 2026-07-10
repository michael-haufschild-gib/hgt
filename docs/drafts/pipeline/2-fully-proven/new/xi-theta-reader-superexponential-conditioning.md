# Correct theta readers have superexponential condition number

- **ID:** xi-theta-reader-superexponential-conditioning
- **Stage:** 2-fully-proven
- **Type:** THEOREM / COEFFICIENT-READER OBSTRUCTION, [PROVED HERE]
- **Date:** 2026-07-10
- **Lean:** formal/GaloisForLFunctions/RHTower/XiThetaReaderConditioning.lean
- **Parent:** xi-theta-critical-log-translation-seam.md

## Medalist lens

The completed trace supplies the Fourier transform in the logarithmic coordinate. The remaining
question is not whether the positive source determines its coefficients abstractly. It does. The
question is whether coefficient extraction is continuous in a topology carried by the completed
trace and strong enough to feed the Perron seam.

Three candidates compete:

1. [CONJECTURE, FALSIFIED BELOW] Nested finite-window transforms admit uniformly bounded triangular
   readers.
2. [BRIDGE] Recover coefficients by successive large-x asymptotics of the theta heat series.
   This is exact but unbounded and uses a boundary limit unavailable to the current Perron norm.
3. [CONJECTURE] Renormalize the trace topology by exp(pi m squared). This may make readers bounded,
   but the renormalization must come from a completed-carrier invariant rather than be installed by
   definition.

The first candidate is the strongest one compatible with the current trace topology, so it is
attacked directly.

## Physical atom

For m at least one, define the strict positive-half logarithmic atom

a_m(u)=1_(0,infinity)(u) 2 exp(u/4-pi m^2 exp u).            (1)

This is the actual m-th term in the positive theta source. It is not the full-line translated
mother and not a Laplace resolvent.

## Theorem A [PROVED]: superexponential physical mass bound

For u at least zero,

0 <= a_m(u) <= 2 exp(-pi m^2) exp(-2u).                     (2)

Consequently

integral_R |a_m(u)| du <= exp(-pi m^2).                     (3)

### Proof

The elementary inequality exp(u) >= 1+u gives

pi m^2 (exp(u)-1) >= pi m^2 u >= (9/4)u,

because m is at least one and pi is greater than three. Rearranging yields

u/4-pi m^2 exp(u) <= -pi m^2-2u,

which proves (2). Integrating its right side on the positive half-line gives

2 exp(-pi m^2) integral_0^infinity exp(-2u)du
  = exp(-pi m^2).

## Theorem B [PROVED]: every critical sample is equally small

For every real frequency w,

|Fourier(a_m)(w)| <= exp(-pi m^2).                          (4)

This is the Fourier L1 bound applied to (3). Thus moving to the completed critical trace does not
restore the lost scale.

## Theorem C [PROVED NEW]: finite-sample reader obstruction

Let w_j be finitely many critical frequencies and c_j complex weights. If

sum_j c_j Fourier(a_m)(w_j)=1,                              (5)

then

sum_j |c_j| >= exp(pi m^2).                                 (6)

### Proof

By (4) and the triangle inequality,

1 <= sum_j |c_j| |Fourier(a_m)(w_j)|
  <= exp(-pi m^2) sum_j |c_j|.

Multiply by exp(pi m^2).

## Theorem D [PROVED NEW]: continuous-reader obstruction

Regard a_m as an element of complex L1 on the logarithmic line. If a continuous linear functional
R_m satisfies

R_m(a_m)=1,

then

norm(R_m) >= exp(pi m^2).                                   (7)

### Proof

Operator norm and (3) give

1=|R_m(a_m)| <= norm(R_m) norm(a_m)_1
  <= norm(R_m) exp(-pi m^2).

Again multiply by exp(pi m^2).

## Attack verdict

- [FALSIFIED] The correct nested-window coordinate admits uniformly bounded finite-sample readers.
- [FALSIFIED] Moving from the physical source to finitely many completed critical samples improves
  the conditioning.
- [PROVED OBSTRUCTION] The unavoidable cost is at least exp(pi m squared), stronger than the
  exp(pi m) scale of the retired Laplace/Blaschke reader.
- [NOT RULED OUT] A reader continuous in a stronger analytic topology involving derivatives,
  strip norms, or an intrinsic exp(pi m squared) renormalization.

The result does not say coefficient recovery is impossible. It says recovery is violently
discontinuous in the L1 physical topology and in every finite critical-sampling scheme.

### Fixed-index audit

The Perron pipeline fixes m before contour depth tends to infinity. Hence exp(pi m squared) is a
finite constant and does not by itself kill the contradiction. The subsequent theorem
xi-theta-heat-reparametrization.md proves that this factor is exactly the x=1 heat-boundary shift.
The obstruction here rules out uniform or weak-topology readers; it does not retire the composite
fixed-index Hardy reader.

## Novelty and significance gate

- **Parent ingredients:** Fourier L1 bounds and continuous-linear-map norm inequalities are
  classical.
- **Novel composition:** the correct completed-trace coordinate from the parent card, the physical
  one-sided square atoms, and their coefficient-reader normalization produce the exact
  exp(pi m squared) obstruction. The earlier exp(pi m) Blaschke condition number belonged to the
  wrong transform.
- **Significance:** the hoped stable triangular reader is now ruled out in two precise topologies.
  Any surviving RH-facing reader must name and justify a stronger topology; it cannot hide
  conditioning inside an unspecified functional.

## Open core

[OPEN CORE] Either find a completed-carrier norm that both:

1. controls the balanced Perron boundary charge; and
2. weights the m-th positive theta atom strongly enough to offset exp(-pi m squared)

without inserting reciprocal-Gamma or exp(pi m squared) decompletion by definition.

Or, for each fixed m, construct the composite inverse-Fourier/heat/Hardy reader and prove that its
finite condition constant is harmless in the balanced Perron depth limit.

## Gates

- [x] 0 -> 1: candidate topologies and falsifiable stability claim isolated.
- [x] 1 -> 2: physical mass, Fourier sample, finite-reader, and L1-reader bounds proved.
- [x] 2 -> 3: formalized and axiom-audited.
- [ ] 3 -> 4: requires the intrinsic stronger topology or a proof that none can feed Perron.

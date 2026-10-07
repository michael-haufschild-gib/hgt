# WP05 result

**Verdict: OPEN.** Assigned canonical-measure settlement problem remains unsolved.

## Canonical boundary trace added in cycle 4

From the original `hW : WeilPositiveFull lam` alone, the normalized completed
producer has an almost-everywhere boundary trace b and satisfies

    integral_R |G(1/2+x+iy)-b(y)| dy -> 0 as x decreases to 0,
    b(y) = exp(i*pi*mu((-y,y])) b(-y),  y>0.

Here mu is the original canonical boundary measure. Diffuse mass, low spectral
mass and the central atom remain present. No atomicity, support gap, boundary
continuity or phase-decay assumption is added. The modulus limit follows from
Herglotz positivity; canonical interval inversion supplies the phase, and the
existing right-edge Gamma decay makes the convergence global in L1.

New source: `WeilWorkSettledPhaseTrace.lean`. The targeted leaf build, final
`lake env lean` source audit and all nine axiom inspections passed. The audited
declarations use only `propext`, `Classical.choice` and `Quot.sound`. Global lint
reports 12 unrelated unreachable modules, with no WP05 error.
Verdict: BRIDGE, using classical boundary inversion. This removes the atomic
representation premise from the trace construction, but the critical-line
coefficient receiver still needs an extension to this measurable trace. Neither
that transfer nor phase settlement has been proved.

## Quantitative phase obstruction added in cycle 3

For an exact positive atomic representation of the original canonical boundary
measure, every fixed candidate phase theta satisfies this dichotomy: either
lambda=Lambda and RH, or there are a,K>0 and arbitrarily large Y such that

    integral_(Y,2Y] |exp(2 pi i S(y))-exp(2 pi i theta)| dy
      >= a Y exp(-K log Y/log log Y).

Here S is the actual strict-cutoff `phaseSum`. No phase-decay hypothesis is
assumed. The new coefficient-free source bound controls the producer's boundary
size; the existing weighted block receiver then gives the obstruction by
contraposition. The logarithmic scale strengthens the obstruction obtained by
contraposing each fixed-power receiver separately.

New module: `WeilWorkSettledPhaseDisorder.lean`. Exact representation, positive
masses, support at least one, local finiteness and weighted summability remain
explicit inputs. They are not produced by the theorem. This is an intermediate
obstruction, not an unconditional solution of the assigned problem, and no broad
scientific novelty is claimed. Verification details are in `EVIDENCE.md`.

## Source estimate added in cycle 2

`WeilWorkSettledPhaseLittlewood.lean` removes the extra coefficient hypothesis
from the corpus's Littlewood bound. For every original full-positive system,

    Re producerLogZeta(hW,sigma,t) <= C log|t| / log log|t|

uniformly for `1/2 < sigma <= 2` and sufficiently large `|t|`. Full positivity
is the only source premise. No atomicity, Euler product, pointwise coefficient
bound, or settled phase is assumed. The proof uses absolute summability at two
and a shorter cutoff in the existing Soundararajan inequality.

The targeted leaf build, final `lake env lean` source audit, and axiom audit passed.
Both new declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
This is a source-growth extension, not a proof of a phase
estimate. Its method is classical; significant scientific novelty is not claimed.
WP05's first phase milestone remains open.

## Audited contribution

Finite positive unit-mass packets have exact phase transport cost. With c=(1+cos q)/2 and atoms at l=1+|a| and r=l+|d|, strict cumulative count S satisfies

    integral_R |exp(2 pi i S(y))-1| dy = |exp(2 pi i c)-1| |d|.

For any finite family, integrated phase defect is at most the sum of these costs; overlapping packets and repeated ordinates are allowed. Half-mass packets attain cost 2|d| while their counting discrepancy from a unit atom at r is at most 1/2 everywhere. Consequently no uniform bound on integrated phase cost follows from that counting discrepancy alone.

New module: `formal/GaloisForLFunctions/RHTower/WeilWorkSettledPhasePackets.lean`. Main statements have no additional mathematical premises: parameters specify explicit spectra, with positivity and support bounds proved internally.

**Novelty assessment: BRIDGE.** This formalizes and sharpens the corpus's existing dipole mechanism; it is not claimed as significant new scientific knowledge, a new infinite spectral class, or a detector for the actual Weil measure. It does not complete WP05's first research milestone. A finite family varying with its width is not a counterexample to asymptotic settlement of one fixed full-positive system.

## Paid and unpaid

- Paid for explicit finite packets: positivity, ordinates at least one, exact strict-cutoff phase identity, finite-family integral bound, sharp single-packet example.
- Unpaid for canonical `boundaryMeasure hW`: atomicity, support restriction, exact atomic representation, source-derived power settlement.
- No theorem supplies existence of a full-positive system, equality with von Mangoldt, or RH.

## Active research conjecture

The existing monotone fractional-mass rigidity theorem may extend from a fixed sublinear power to C(T)=o(T). Its current proof does not: every fixed strip exponent nu>0 loses T^nu. The next source-sensitive attack must retain that fractional atoms occur at zeros of the producer when estimating contour top edges. Merely varying nu without uniform constants is invalid.

Cycle 2 now provides a quantitative logarithmic envelope from the original source.
It still does not suffice for C(T)=T/log T. The next exact transfer candidate is
fractional mass bounded by `T exp(-log T/sqrt(log log T))`; this candidate is not
yet proved or produced by full positivity. A collective cancellation estimate is
still needed to reach arbitrary sublinear fractional mass.

This is a prospective route toward the same constant-phase target, not a second AP project. It is not asserted true or formalized. Exact evidence and verification are recorded in `EVIDENCE.md`; paper arguments and the remaining gap are in `PROOF.md`.

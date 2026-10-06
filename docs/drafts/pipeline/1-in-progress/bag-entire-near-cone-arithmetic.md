# BAG: entire shrinking near-cone arithmetic cancellation

- **ID:** bag-entire-near-cone-arithmetic-30az
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** bag-global-conormal-localization.md; ChiCubicNearConeReduction; ChiPrimeGaussianCubicIntegerDefect; ChiRamanujanTransverseProfileFibres.
- **Statement:** The norm of bagCubicNearConeAction N, multiplied by log²N/N, tends to zero on the full original natural scale.

## Hard target

The COMPLETE projected exterior is now proved rapidly decreasing. The
original sharp cubic differs negligibly from the ENTIRE retained action.
This card must prove that action cancels. It cannot replace it by the
already closed positive exact-cone action, omit nonzero defects, or
assume a source norm or an inverse-defect bound. Growing mixed moments,
cofactors and deterministic common-height BAG return remain later hard
problems even after this cubic target.

Actual near test is FourierInv(chi(D/epsilon)*Fourier(A_N)), with
D(xi)=xi_2+xi_0*xi_1, epsilon=N^(-1/8), H=N^(1/4). The source is the
literal complete critical prime set through2N, with its actual projector
level floor(2N)+1. Both projectors act after the geometric split.

## Corpus basis

- ChiCubicExteriorSource: COMPLETE source bound, uniformly ALL prime sets
  and moduli, and arbitrary-power decay of the actual entire exterior.
- ChiCubicNearConeReduction: exact tube Fourier test; full natural-scale
  exterior decay and sharp-cubic reduction. Final audit recorded below.
- ChiPrimeGaussianCubicIntegerDefect: all lattice lifts are equivalent to
  the three exact congruences in BAGDefectIndex; normal coordinate is
  d/Q², with physical phase exp(-2*pi*i*r*d/Q²).
- ChiRamanujanTransverseProfileFibres: prime-height zero fibres retain both
  axes and their intersection; nonzero fibres retain the full inverse
  curve and exact two-frequency Kloosterman pairing. These local fibres
  are not yet the global normal-coordinate source.
- ChiCubicCoveredMellinCancellation: covered positive EXACT-cone action
  cancels. Its scope is smaller than the tube retained here.

Search evidence: focused37777, nonpartial67977,index/coverage1266330,
current1266331,compiler pending51621/stale2660/error2,noinventoryerrors.
All20 candidates and20 source arguments inspected; proposed unrelated
confocal/torsion ingredients from deep3709 rejected. Source declarations
above were read directly; no claim is based on search-generated proof ideas.

## Next conjecture and attempted mechanism

Keep the signed normal sum before absolute values. Set L=logN and write
Xi_N(x,y,t)=(x,y,t/N-x*y),
G_N(x,y,t)=(L³/N)*Fourier(A_N)(Xi_N(x,y,t)). The target is the complete
projected source applied to chi(D/epsilon)*G_N(xi_0,xi_1,N*D), divided by L.
This is an algebraic rescaling of the actual test, not a new assumption.
The normal physical height is r/N in[1,2].

Attack a signed fixed-profile law and a uniform operator estimate in a
space that retains this height support and the coupled tangential profile;
then prove actual moving-profile convergence in that SAME space. All three
are producer obligations, not hypotheses to export as an RH receiver.
The exact congruence/source decomposition must precede importing local
inverse-curve cancellation. Its cost must remain uniform in the growing
radical-square modulus and retain both shifted projector terms and their
intersection. A Schwartz-seminorm bound alone is already known and does
not pay the growing near-cone profile.

First rejected shortcut: freezing exp(-2*pi*i*r*d/Q²) at d=0 does not give
small error throughout the tube: r is of order N and |d/Q²| can reach
N^(-1/8). The naive difference estimate costs N^(7/8). This only rejects
that estimate; it does not falsify the cancellation conjecture. Next work
must exploit the signed normal oscillation rather than erase it.

## Gates

- [x] Exact original source and unconditional target specified.
- [ ] Actual global normal-source law, with every congruence/projector paid.
- [ ] Signed uniform estimate and actual moving-profile application.
- [ ] Complete Lean proof; leaf/axiom/umbrella/lint audits.

## Log

- 2026-10-06,30az: exterior attachment succeeded. This is the remaining
  hard arithmetic sector, not another exterior-bound optimization.

- Final direct5368: ChiCubicNearConeReduction PASS; earlier combined-import
  scratch85390 PASS. Exact original sharp reduction is now checked.

30az final certificate: axiom85038 PASS, all25 public theorem endpoints
use only propext,Classical.choice,Quot.sound. The same scratch imports
both BAG branches and proves equality of old/new actual constructors
on the overlapping scale domain. All owned processes are terminal.
P3:bag-complete-arithmetic-exterior records the complete theorem, paper
proof and audits. RH goal remains active; entire near-cone arithmetic
continues in P1:bag-entire-near-cone-arithmetic.

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

## Continuation31az — testing the full normal-source transfer

Previous30az is verified progress: COMPLETE arithmetic exterior and original
sharp reduction. Current target remains the entire signed near-cone action;
no new cancellation theorem is claimed in this continuation yet.

Corpus24070 nonpartial67982,index1266455,coverage1266446/current1266456;
pending51624/stale2660/error2,noinventoryerrors. Corpus69949 nonpartial67982,
index1266482,coverage1266472/current1266483,samecompiler counts. All20
candidates and20source arguments and ingredients inspected. The exact46
source references to primeGaussianCubicOffDiagonal/bagCubicNearConeAction
were enumerated; none is a full cancellation theorem. No theorem absence
was inferred from semantic search alone.

Attempt1: annihilate nonzero normal fibres by local prime weights. Current
ChiPrimeGaussianCubicLocalAxisRigidity rules out using this as the complete
saving: the actual local axes retain (1-r^-2) times the WHOLE source,
while the signed inverse fibres retain r^-2 times it. This is an existing
verified obstruction, not new progress. It concerns local prime-height
fibres, not the global normal coordinate. Do not repeat its proof.

Attempt2 under examination: fixed-profile normal-source convergence plus
an ordinary Fourier Sobolev operator bound. Exact third-height sampling
in bagLabelledThirdGrid_block makes the required topology delicate.
For a one-dimensional normal profile psi, compact support of Fourier psi
in a fixed positive HEIGHT band does not bound its Fourier value at an
individual height by any ordinary H^k norm of psi. A narrow height bump
b_delta centered at that height has b_delta(r)=1 and weighted L2 mass
O(delta); psi=FourierInv(b_delta) has every fixed ordinary H^k energy
O(delta). This is a paper test of the proposed trace norm, not a claimed
formal no-go for the entire projected source. In particular, normal
coordinate WEIGHTS and normal DERIVATIVES must not be conflated.

Positive replacement to prove and then apply, rather than abandoning the
signed source: a scale-dependent COMPLETE height sampling inequality,

  (1/N) sum_n ||h(n/N)||^2 <= C (integral ||h||^2
                              +N^-2 integral ||h'||^2).

It should hold also for Hilbert-valued h, with one constant. All prime
heights form a subset; logarithmic labels can be normalized by logN.
The derivative penalty is essential: it pays actual narrow edge changes
at scale delta=N^-3/4, for which N^-2*delta^-1 tends to zero. This would
supply a valid normal-height trace component for the SAME full-source
estimate; it alone does not prove signed tangential arithmetic cancellation.
A valid proof must then incorporate all complementary prime factors and
both projectors, not call this one-dimensional trace the full operator.

Paper proof of the sampling component: on each disjoint unit cell around
an integer, FTC and Cauchy-Schwarz bound the squared sample by twice the
cell integral of ||h||²+||h'||². Sum EVERY cell before scaling. Fourier
Plancherel translates the derivative penalty into a normal-coordinate
second moment, retaining its N^-2 factor. This is the replacement norm
obligation now being checked against corpus APIs before formalization.

Height-trace search69190 partial(decomposition),67986 indexed,
index1266610,coverage1266598/current1266613,pending51628/stale2660/error2,
noinventoryerrors. All20candidate/source statements and ingredientsets
inspected; proposed determinant-line squareIntegral ingredients are
inapplicable. Relevant actual sources: Schwartz Fourier Plancherel,
ChiCubicMellinTrace's admitted weighted Cauchy-Schwarz, and the exact
prime-height selection above. No Lean source or build has started31az.
All three owned searches are terminal; logs/JSON retained.

31az continuation correction: Gallagher already supplies the general sampling
ingredient. No standalone derivative-budget wrapper was added; it would not
close the signed source. The ordinary-Sobolev bump test above concerns arbitrary
profiles, and must NOT be applied to the actual truncated normal slice without
checking its support.

New constructive conjecture: the literal retained tube supplies an exact
normal sampling isometry. For fixed tangential x,y put
psi(D)=Fourier(near_epsilon f)(x,y,D-x*y). The already audited cutoff identity
forces psi(D)=0 for |D|>=2epsilon. If epsilon<=1/4, the full integer-height
Fourier samples satisfy sum_r |Fourier psi(tau+r)|²=integral |psi|², for EVERY
real shift tau. This is the corpus WindowTransformSamplingParseval identity
on an interval of length one, with its conventions explicitly converted.
It has no growing derivative penalty and applies to the actual shrinking
tube eventually on the full original natural scale. The normalized critical
height weights M_P(|r|)/log(1+|r|) lie in[0,1], so every finite labelled height
trace is controlled by that SAME energy, uniformly in P. This is an actual
normal-source component, not a bound for the complete tangential action.
Translations from the two projectors still require an exact attachment;
their terms must not be erased by this scalar statement.

Paper proof is dependency-closed on nearConePhysical_fourier, the exact bump
support, hasSum_norm_sq_paperFT_grid, and the critical multiplier bound.
Formalization is starting in an owned /tmp file; no new result audited yet.
Joint search79412 nonpartial67993,index1266754,coverage1266758/current1266759;
normal-band search14549 nonpartial67993,index1266764,coverage1266758/current1266764.
Both pending51635/stale2660/error2, no inventory errors. All20 candidate and
20 source statements and ingredient suggestions inspected. The joint query's
periodic-prefix/prime-reciprocal-square ingredient set does not provide the
trilinear saving. The normal-band query gives the actual sampling Parseval
source, subsequently read directly. Both search processes terminal0.

31az positive result: ChiCubicNearConeHeightTrace passes complete
scratch44274 and final direct89755, without diagnostics or heartbeat
changes. Exact full-height Parseval, every real grid shift, BOTH
contraction translations including mixed u*v, and the COMPLETE weighted
critical height square trace are formalized. Original natural-scale
epsilon=N^-1/8 is attached eventually for EVERY physical Schwartz input.
P3:bag-near-cone-normal-height-isometry records exact scope and proof.
Index35025 passes; lint21018 has no finding in the new leaf, but27 unrelated
unreachable modules and367 size warnings. Final axiom44654 passes all10
public theorem endpoints with only propext,Classical.choice,Quot.sound.

Evaluation: this corrects and closes the normal trace obstruction for the
actual truncated tube. It does NOT close the hard signed tangential
arithmetic estimate. No full cubic, higher-moment or RH closure follows
from a quadratic norm bound alone. Do not repeat31az's generic height-budget
search as the next turn's main task. Continue the complete signed
two-tangential source across all growing rational modes, retaining
cross-height interactions and both projectors before taking norms.

# BAG full third-prime physical-height action

Route: full signed physical cubic, retaining both tangential inverse fibres.
Status: dependency-closed paper proof; Lean production and axiom audits pass.
No signed asymptotic saving or RH proof.

For the entire critical atom source define C_P F(x,y,z)=sum_c w_c
F(x,y,z+theta_c), with the original finite critical prime weights and exact
rational nodes. At fixed real xi,upsilon,z, partial Poisson expresses each
complete third Fourier-lift block as a finite physical-height sum. Expanding
exp(2*pi*i*n*(z+theta_c)) splits off the source phase. Both sums are finite,
so the existing exact atom identity evaluates sum_c w_c exp(2*pi*i*n*theta_c)
as the full distinguished-prime multiplier M_P(|n|), for every integer n.
Thus the contracted block is exactly

  sum_(ceil(a)<=n<=floor(b)) M_P(|n|)*exp(2*pi*i*n*z)*g_(xi,upsilon)(n).

Here g is the full two-coordinate physical slice; no Gaussian, logarithmic,
window or reciprocal factor is removed. No separability is assumed.

To contract the full lifted test, start from absolute summability of its
entire three-dimensional Fourier lattice. Product summation gives convergence
of each whole third-lift block in the second lift, and convergence of their
second-lift sums in the first lift. Multiplication by each fixed atom weight
preserves this. The finite source sum can therefore move inside both outer
lattice sums. Apply the block identity there. The physical-height sum stays
INSIDE both tangential sums; individual-height summability is not assumed.

C_P is linear and commutes with every literal rational translation: adding
the third atom node commutes with adding the translation vector. Therefore
it commutes with each finite translation average and with their complementary
composition (the original noncontracting projector). The critical triple
weight factors into the three original single-coordinate weights. Finite
reassociation now expresses the original complete triple action as the first/
second critical atom action on C_P F. Applying the commutation identity and
the contracted lifted-test formula retains BOTH projectors and every atom.

For the actual positive integer band, the proved critical range multiplier
is the prime logarithm. Both projector translations remain (x+u/D,y+v/D,
z-u/D-v/D), so every height keeps its full mixed translation phase and the
two separate shifted tangential profiles. The actual cutoff family supplies
all support conditions unconditionally and preserves the original negligible
sharp/smooth edge error. This is an exact prime-height source identity.

Remaining hard target: signed growing cancellation of this full action,
including the nonzero negative cone pole and every near-cone/tail sector,
at complex norm o(N/log^2 N). Prime selection, source contraction and a fixed-
modulus inverse-fibre operator do not themselves give this estimate. Growing
moments, moving cofactors, common-height self-return and RH remain open.

## Individual-height summability, stronger successor

For D=floor(2N)+1 and n,r in the positive integer physical band, |n-r|<D.
Hence D divides |n-r| exactly when n=r. Multiply the exact finite-height
Poisson polynomial by exp(-2*pi*i*r*u/D) and sum u=0,...,D-1. Finite torsion
orthogonality therefore recovers g_(xi,upsilon)(r), with coefficient 1/D.
This identifies each individual physical slice with a FINITE linear
combination of full third-lift blocks, at translations u/D.

Reassociate the absolutely summable full Z^3 Fourier series as (Z^2)*Z.
The sums over its third coordinate form an absolutely summable function
of the two remaining integer lifts. Apply finite linear combination to the
previous coefficient formula. Each individual-height slice is now jointly
absolutely summable over Z^2. Finite height sums and the two infinite lift
sums can consequently be interchanged. Linearity of both projectors and
the remaining finite pair source gives the exact sum of whole projected
physical-height actions, weighted by log(r) on prime heights and zero
otherwise. This is the justified entry to prime-by-prime full inverse-fibre
coupling; the eventual signed saving remains a separate hard problem.

## Lean audit — continuation01aj

ChiPrimeGaussianCubicPrimeHeight:490 lines/28 public declarations. Scratch12255
passes empty; final production71595 passes empty with lake --old env lean on
this leaf and its explicit .olean output. Axiom99790 checks all28, standard3
only. The earlier axiom probe printed the same dependencies but its unrelated
name checks needed explicit universe levels; the corrected whole probe passes.
No production proof was changed for that probe correction.

Index62284 passes; all28 public declarations appear in LEAN_API, umbrella
import once. Lint78872 reports26 unreachable modules outside this leaf and174
large-file warnings, no proof-debt or new-leaf finding. Global lint is not clean.
Only required missing imports were rebuilt, serially, with no source edits.
No full/umbrella build, added axiom, premise-bearing RH claim, numerical
computation, limit hack or subagent. Completed scratch sources cleaned; logs
and corpus search JSON retained.

Main exact endpoints: bagThirdPhysicalSlice_eq_torsion,
summable_norm_bagThirdPhysicalSlicePairs,
bagPhysicalPrimeHeightAction_eq_heightSum,
primeGaussianCubicSmoothedOffDiagonal_eq_primeHeight and the hypothesis-free
exists_bagPhysicalPrimeHeightFamily. The latter targets the FINITE OUTER
prime-height sum bagResolvedPrimeHeightAction and retains the original
log^2(N)/N norm error from the sharp cubic.

Assessment: the exact third-source contraction and individual-height exchange
gaps are closed. The positive analytic advance is finite coefficient extraction
from full lift blocks, giving per-height joint absolute summability without a
new parameter-integral smoothness premise. Remaining attack: attach each whole
height profile to the full local prime-square source, transfer both actual
label exclusions, then prove the growing signed pole/near-cone/tail saving.
The nonzero negative cone residue cannot be discarded. Growing moments,
moving cofactors, common-height self-return and RH remain open. Goal ACTIVE.

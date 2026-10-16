# CHMD: spatial localization in the maximal operator domain

Status: FORMALISED. Compactly supported operator cores proved for both actual generators. Smooth operator cores and RH remain open.

## Obstacle

Compact form density does not imply compact operator-core density. The actual
arithmetic and stationary generators have been constructed and identified up to
a bounded perturbation. Their domains must now be localized without assuming
boundedness or smoothness of a domain vector.

## Conjecture and paper mechanism

Every bounded Lipschitz spatial multiplier preserves the maximal generator
domain. Multiplication by the established cutoffs chi_n converges in generator
graph norm, producing compactly supported representatives of arbitrary domain
vectors. This removes the obstruction at infinity; smooth local approximation
is a separate remaining problem.

Let eta(dt dx)=t kappa(t) Theta(x) Theta(x+t) dt dx for t>0. Both endpoint
pullbacks from mass L2 to eta L2 are bounded: Theta is globally bounded,
cosh>=1, and integral t kappa is finite. For chi bounded Lipschitz, put
b_chi(t,x)=(chi(x)-chi(x+t))/t. Then multiplication by b_chi is bounded on
eta L2. The exact antisymmetric pairing

  E(chi u,v)-E(u,chi v)
  = integral b_chi [u(right)v(left)-u(left)v(right)] d eta

defines a bounded source-space commutator. The corresponding form identity
proves maximal operator-domain admission of chi u. For chi_n, b_chi_n is uniformly bounded and tends pointwise to zero.
Dominated convergence gives strong convergence of the moment multiplier and
therefore of its two endpoint factorizations. No quantitative decay estimate is
needed. The prime generator is bounded, so its cutoff commutator also tends
strongly to zero. Consequently both
u_n and L u_n converge in mass L2. The stationary generator follows from the
already-proved bounded perturbation identity.

## Completed work

1. Prove actual first-moment endpoint admission and bounded pullback maps.
2. Construct cutoff graph multipliers and exact bounded commutator.
3. Prove generator-domain localization and compact-support graph-core density.
4. Audit each new leaf with plain Lean and all-declaration axioms; wire finished
   leaves, run formal lint, and clean owned scratch.

## Validation

Four new leaves, 652 lines, 69 declarations:
- CHMDArchMomentPullback
- CHMDOperatorCutoffForm
- CHMDOperatorCutoffCommutator
- CHMDCompactSupportOperatorCore

Each targeted `lake --old build` passed. Final plain `lake env lean <file>`
passed on all four leaves with empty output. All 69 declarations were audited
from /tmp; only propext, Classical.choice, Quot.sound occur. API probes passed.
Source hashes remained unchanged. All four umbrella imports occur exactly once;
all 69 declaration names are unique in the CHMDDoobGraph source namespace.

The capstone proves exact graph closure, not just a conditional approximation
criterion: `arithmeticGenerator_compact_graph_closure` and
`stationaryGenerator_compact_graph_closure` (lines 136 and 151).

Global formal lint exits 1 solely for four other unwired modules:
CHMDFarFieldEnergy, CHMDPrimeWindowTail, XiGaussianHeatRegularTransfer,
HTGeometry.MomentNormalBlockRecurrence. No proof-debt lint error. Those modules
were not changed or wired by this task. No full/umbrella build or commit/push.

No unconditional RH proof claimed.

## Exact maximal-domain step

Write R=(I+L)^(-1), p=rieszLift(w), u=Rw. The cutoff graph vector Mhat_n p
satisfies, for every full graph test q,

  <Mhat_n p,q>_graph = <M_n w + C_n u, source(q)>_mass.

Riesz uniqueness gives R(M_n w+C_n Rw)=M_n Rw. Thus M_n maps range(R)
into itself and L(M_n u)=M_n(Lu)+C_n u. Strong multiplier convergence
and C_n u -> 0 prove graph convergence. The chosen representative
chi_n(x) u(x) has compact support, regardless of the source's size or
regularity. For G=L-K with bounded K and the exact common domain, the same
sequence converges together with G's image.

This proves compact-SUPPORT core approximation, not compact-SMOOTH core
approximation. The remaining obstruction is entirely local regularization.

## Remaining local smoothing mechanism (not yet formalised)

The result permits a different continuation from the global half-density
essential-self-adjointness proposal. First localize u in Dom(G), so f=Theta*u
has compact support. Construct the correct unweighted stationary generator A
with kernel kappa (not the Gamma-clock kernel kappa/t). Show f belongs to
Dom(A): localize arbitrary stationary form tests by a cutoff equal to one near
support(f); the local pairing is supplied by G's actual form identity, and
the complementary separated-support pairing is a bounded L2 tail functional.
Then compact convolution mollifiers should commute with A on its maximal
domain, yielding f_epsilon -> f and A f_epsilon -> A f in ordinary L2.
Division by the strictly positive Theta on the common compact support gives
smooth compact u_epsilon. The bounded factor Theta/cosh transfers generator
image convergence back to the mass space. Diagonalize after the proved spatial
cutoffs. These are future obligations, not consequences already formalised here.

Do not assert the global identity Dom(G)={u:Theta*u in Dom(A)}. The proposed
ordinary-domain admission applies after compact spatial localization.

Cleanup complete: all owned jobs terminal; 14 exact owned scratch files removed.

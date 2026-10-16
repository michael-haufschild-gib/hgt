# CHMD: spatial localization in the maximal operator domain

Status: IN PROGRESS. RH remains open.

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
proves maximal operator-domain admission of chi u. For chi_n, b_chi_n tends
uniformly to zero because its Lipschitz constant is O(1/n). The prime generator
is bounded, so its cutoff commutator tends strongly to zero. Consequently both
u_n and L u_n converge in mass L2. The stationary generator follows from the
already-proved bounded perturbation identity.

## Work plan

1. Prove actual first-moment endpoint admission and bounded pullback maps.
2. Construct cutoff graph multipliers and exact bounded commutator.
3. Prove generator-domain localization and compact-support graph-core density.
4. Audit each new leaf with plain Lean and all-declaration axioms; wire finished
   leaves, run formal lint, and clean owned scratch.

## Validation

Pending. No unconditional RH proof claimed.

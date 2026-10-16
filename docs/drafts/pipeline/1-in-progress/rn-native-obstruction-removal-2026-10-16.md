# RN native obstruction removal

Status: research in progress; no new theorem claimed.

Objective: remove a structural obstacle in RN with an unconditional theorem,
not an estimate, RH equivalence, or receiver. Use current Lean corpus only.
No numerical experiments, external search, novelty audit, or full builds.

## Plan

1. Identify the frontier from corpus search and actual Lean declarations.
2. Conjecture an exact structural statement; attack it before formalization.
3. Complete its paper proof, then formalize and wire the new leaves.
4. Audit each leaf directly, inspect axioms in /tmp, run formal lint, clean up.

The update_plan tool is not available in this session; this card records the plan.

## Verified starting evidence

- PaperThetaNativeGrushin: an invertible augmented pencil on the whole
  bounded-continuous native space, using a genuine compact counter-source.
- PaperThetaNativeResonantSplitting: exact one-step range and kernel at every
  resonance; zero-trace particular solution and actual theta moment defect.
- PaperThetaNativeEntireRepair: entire repair of the original uniform pencil.
- PaperThetaNativeMeyerCompleteness: full generalized root blocks already
  equal original finite Meyer packets. This source is modified by pre-existing
  work; do not edit it or claim its result as a contribution here.
- PaperThetaNativeSourceSynthesis and PaperThetaNativeCohomology: faithful
  whole-source realization after genuine Gaussian regularization.
- ThetaRenewalCausalMoments: full prime/Gamma/polar action on every lower
  causal jet equals its next whole source moment, including actual Xi
  multiplicities.

## Conjecture loop

C1: classify every bounded-continuous generalized Xi mode by original Meyer
jets. Verdict: ALREADY PROVED in PaperThetaNativeMeyerCompleteness. Do not
duplicate it.

C2: remove Gaussian regularization from whole-source native synthesis.
OPEN: reciprocal Xi introduces exponential contour growth, whereas the
original source has rapid polynomial vertical decay. Existing summability
proof cannot be specialized to zero regularization. No impossibility claimed.

C3 under investigation: construct the full confluent source/cusp projection
on arbitrary native forcing, retaining every Xi multiplicity and exact
solvability at repeated resonance. Determine whether current scalar moment
repair and original-source duality already imply a stronger result.

## C3 paper proof

At an actual Xi point put N = nativePencil, B = the first column of the
Grushin inverse at zero prescribed trace, v = its unit-trace kernel vector,
b = the compact counter-source, c = actual theta moment / counter-mass,
and L = the actual resolvent tail trace. Existing inverse identities give

    NB = 1 - b c,  BN = 1 - v L,
    Nv = 0, cN = 0, Lv = 1, LB = 0, cb = 1.

Let E be the full generalized nullspace, whose dimension m is the actual
Xi multiplicity by current native completeness. Write w_j = B^j v and
a_j = c(w_j). The first nonzero a_j occurs exactly at j=m-1:

1. If every a_j vanished, all w_j would form an infinite lowering chain
   in E with nonzero bottom, contradicting finite dimension.
2. If n is the first nonzero index, w_0,...,w_n are an independent chain
   in E, hence n+1 <= m.
3. O(x) = (c B^j x)_(0<=j<=n) satisfies O(Nx)_0=0 and
   O(Nx)_(j+1)=O(x)_j, because all earlier a_j vanish. Its kernel is
   N-invariant. Its intersection with ker N is zero since ker N is Cv
   and O(v)_n=a_n != 0. Induction on nilpotence height shows O is
   injective on E. Thus m <= n+1.

Consequently the m actual integral readings O:E->C^m are an isomorphism.
Define P = inclusion * (O|E)^(-1) * O on the WHOLE native space. Then
P^2=P, range P=E, ker P=ker O, and PN=NP. This constructs the full
projection from source readings, without a simplicity, separation, finite
forcing, positivity, or projection-existence premise.

For W=ker O and a=a_(m-1), set

    H y = B y - (c B^m y/a) v.

For y in W, NH y=y. All m readings of H y vanish: the first m-1
shift to readings of y; the last cancels exactly against a. Kernel
uniqueness gives HN x=x on W. Iteration therefore solves N^k on W at
every order. On E, N is nilpotent; (1+N)^(-1) is its finite geometric
series. Combining both sectors yields an explicit invertible repair
N+P on the whole space, deleting exactly the full original Xi block.

All operators above are bounded in the original uniform norm: B,c,L are
bounded, and inversion only occurs in the finite-dimensional observed
block. The finite correction is an actual original native Meyer packet.
BV forcing is preserved by B (the existing literal Grushin solution and
the fixed Green equation) and by finite packets; hence the repaired
solutions retain compact AC and full arithmetic admission after the
fixed Green operator. This last transport must be checked directly in
Lean, not inferred from uniform-norm boundedness.

Verdict: survives the algebraic attack. This targets full original-space
resonant projection/solving, not the still-open directed arithmetic sign.

## Audit constraints

Pre-existing changes: frontier map, RHTower umbrella, native root transport
and completeness, XiNewtonDiscCurvature, and unrelated cards/report. Preserve.
Search reports may be source-only or stale: declarations require direct Lean
audit before relying on a new formal result.

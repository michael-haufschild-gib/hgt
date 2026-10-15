# Actual Hurwitz zero graph and Kummer root-domain pinching

This is a source-deformation theorem within DR. It does not certify the
zero-free half-strip or replace that goal. Its paper proof and exact Lean
formalization are complete. All eight new source modules check without
diagnostics. Axiom audit passes; repository lint has unrelated umbrella
reachability failures recorded below.

## Exact statement

Write H(s,a) for the repository's canonical continued Hurwitz zeta. For
every zero rho of Xi, there is a neighbourhood V of rho and a holomorphic
function A on V with A(rho)=1 such that, near (rho,1),

    H(s,a)=0 iff a=A(s),
    partial_a H(s,A(s)) != 0,
    ord_rho(A-1)=ord_rho(zeta)=ord_rho(Xi).

In particular every critical-line zero has simple Hurwitz zeros at shift
parameters arbitrarily close to 1 with s strictly inside the right half-strip.
Thus no fixed positive-width complex neighbourhood of the shift a=1 over
the entire right half-strip admits a holomorphic d-th root of H for d>1.
This failure persists even if RH is true. A construction via this family must
allow its shift neighbourhood to shrink toward the critical-line zeros.

## Corpus audit and verdict

`XiHurwitzAnchorTransversality.lean` already proves H(rho,1)=0 and
partial_a H(rho,1)=-rho*zeta(rho+1) != 0, for every Xi zero and every
multiplicity. `Hurwitz/AnchorTransversality.lean` proves all positive-order
anchor derivatives. `XiHurwitzAnchorJetProjectiveReflection.lean` already
shows that a common projective reflection law for those jets is equivalent
to the critical-line equation; it does not produce that law.

The joint local zero graph and the resulting fixed-width root obstruction
were not found in the inspected source/corpus searches. They are applications
of holomorphic implicit-function geometry, not a claim of a new scientific
principle or a solution of RH. Verdict on fixed-width root transport: FALSE.
Positive survivor: the exact local graph and multiplicity of its contact
with the arithmetic slice a=1.

## Dependency-closed paper proof

Near any (s0,1) with Re(s0)>0 and s0 != 1, zero-degree regularization gives

    H(s,a)=zeta(s)+sum_{n>=0}[(n+a)^(-s)-(n+1)^(-s)].

Fix a compact exponent neighbourhood with Re(s)>=delta>0 and a shift disk
|a-1|<=r<1. Factor each summand by (n+1)^(-s), putting
y=(a-1)/(n+1). On the compact exponent set times |y|<=r, the derivative
in y of (1+y)^(-s) is bounded: its base stays in the right half-plane.
Integrating along the segment from 0 to y bounds the bracket by C|y|.
Hence the summand is bounded by C*r*(n+1)^(-delta-1), a summable sequence.
Every summand is jointly holomorphic. Normal convergence and holomorphy
of zeta away from 1 establish joint holomorphy of H near (s0,1).
This is a convergence justification for the source family, not a zero estimate.

At rho, the nonzero derivative in a is the already proved anchor derivative.
The holomorphic implicit-function theorem therefore supplies A, and shrinking
the neighbourhood preserves the nonzero derivative. Analytic division in a
gives H(s,a)=U(s,a)*(a-A(s)), with U holomorphic and nonzero near (rho,1).
At a=1, zeta(s)=U(s,1)*(1-A(s)). The unit has analytic order zero, so A-1
has exactly zeta's order. Xi differs from zeta by a nonvanishing completion
factor in this neighbourhood, proving the last equality without simplicity.

Choose any known critical-line Xi zero rho. For any fixed shift radius r>0,
continuity gives |A(s)-1|<r for s sufficiently close to rho. Such s can be
chosen with 1/2<Re(s)<1. At that exponent, H(s,a) has a simple a-zero at
A(s). A holomorphic d-th root on the whole shift disk would give its zero
order divisible by d, contradicting order one. This proves the obstruction.

## Completed formalization

1. Prove a compact-parameter normal-convergence bound for the actual
   zero-degree Hurwitz remainder, using the existing factorization lemma.
2. Establish joint regularity near the anchor; use the actual source, not
   its affine Taylor approximation.
3. Apply the complex implicit-function theorem and identify the contact order.
4. Derive the fixed-width root obstruction from a known critical-line zero.
5. Audit current source, axioms, imports, lint, and indexes as applicable.

The exact source theorem is
`RHTower.exists_analytic_hurwitz_zero_graph_with_contact_order` in
`formal/GaloisForLFunctions/RHTower/XiHurwitzAnchorContactOrder.lean`.
The unconditional obstruction is
`RHTower.not_forall_exists_hurwitz_shift_disk_power_root` in
`formal/GaloisForLFunctions/RHTower/HurwitzRootTubePinching.lean`.
The latter uses the existing non-numerical Hardy theorem to supply a
critical-line zero. Both declarations have been checked from current source.

No premise encoding RH, root existence, or zero-free deformation is permitted
as an input to the final source theorem. DR's main gluing problem stays open.

### Formal bridge: normal convergence gives strict differentiability

The multivariable regularity step can avoid explicit exponent derivatives.
For analytic summands f_n on B(c,2r), assume ||f_n|| <= u_n there and
sum u_n < infinity. For x in B(c,r), the ball B(x,r) lies in B(c,2r).
On this ball ||f_n(y)-f_n(x)|| <= 2u_n. The Banach-space complex Schwarz
lemma gives ||Df_n(x)|| <= 2u_n/r. This is a summable uniform derivative
bound. Termwise Frechet differentiation therefore holds on B(c,r).
Each Df_n is continuous there, and its normally convergent sum is
continuous. Hence the sum is strictly differentiable at c. This applies
to the actual remainder on a sufficiently small product-norm ball.
No zero location or absence enters this regularity lemma.

For contact order, a formal route avoids multivariable analytic division:
strict differentiability compares H(s,1) and H(s,A(s)) at the same exponent.
Their input difference is exactly (0,1-A(s)); thus

    zeta(s) - c*(1-A(s)) = o(1-A(s)),
    c = partial_a H(rho,1) != 0.

If A-1 is locally zero, so is zeta and both local orders are infinite.
Otherwise isolated zeros give 1-A(s) != 0 on a punctured neighbourhood.
The quotient zeta(s)/(1-A(s)) tends to c. It is meromorphic, so its finite
nonzero limit removes the singularity to an analytic unit. Multiplication
by this unit preserves analytic order. This proves the same exact contact
law using the established joint C1 regularity.

## Final verification

All eight new source modules were checked directly with `lake --old env lean`
from `formal/`; dependency objects were written only when needed. No full or
umbrella build was run. The final source audit of the root-tube theorem plus
six `#print axioms` commands in `/tmp/hgt_dr_hurwitz_graph_final_audit.lean`
exited 0. Every audited declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

All eight modules are wired into their theorem-area umbrellas. The index
command completed with exit 0. Repository-wide `scripts/formal_tools.py lint`
exited 1, with only these errors, all outside this task's new modules:

- `RHTower.CHMDStage1MultiplicativeResolventAndClampedBeam` unreachable from umbrella.
- `RHTower.LogSineQuantileClock` unreachable from umbrella.
- `RHTower.PolarConeArchimedeanCriterion` unreachable from umbrella.

Existing large-file warnings also remain. No foreign module was edited to
clear the shared gate. No numerical computation or external search was used.

Anti-theatre: this is a fully formalized source-deformation obstruction and
its exact positive survivor. It is not a zero-free half-strip certificate,
an RH proof, or a claim of a new mathematical field. The outstanding DR task
is still to construct the actual Euler-marked root sections and prove their
local monodromy vanishes. Total-divisor smoothness and a fixed-width Hurwitz
tube cannot supply that step.

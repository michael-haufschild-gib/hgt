# BAG growing-prime near-pole source

Continuation01an. Hard target: the actual `criticalCompletedConeEuler`
with BOTH growing prime cutoff and moving Mellin arguments. Fixed-prime
double residue (ag.11) does not justify this exchange. The physical cone
pairing (ag.13) uses real parts 2; the untagged local factor there tends to
3, so a prime-uniform bound on that line cannot follow by multiplying
bounded local factors. This observation does not prove divergence of the
full tagged sum: cancellation between actual labels must be retained.

Conjecture under investigation, not a theorem: P_X=primes<=X, L=log X,
s=1+lambda/L, t=1+mu/L. For lambda,mu in compact subsets of positive real
half-planes, the pole-removed actual completed source converges to
exp(-3 gamma)*exp(J)*I_A*I_B*I_C, where

J=integral_0^1 (exp(lambda u)+exp(mu u)
  -exp((lambda-mu)u)-exp((mu-lambda)u))/u du;
I_A=integral_0^1 (1+exp((lambda-mu)u)-exp(lambda u)) du;
I_B=integral_0^1 (1+exp((mu-lambda)u)-exp(mu u)) du;
I_C=integral_0^1 (1-exp(lambda u)-exp(mu u)) du.

Corpus sources: ChiRamanujanCofactorPole, WeightedCubicLocal,
WeightedDistinguishedCubic, BalancedLabelTrace; actual physical family and
pairing in ChiPrimeGaussianCubicConeMellin and Transverse. The conjecture
comes from their exact local formulas, not a replacement source. All
normalizations and signs remain subject to symbolic Lean checking.

Proof architecture: z=1/p, a=p^(-(s-1)), b=p^(-(t-1)). Remove both local
cofactor denominators and derive the exact local rational expressions for
five allowed tag patterns: none, first, second, third, first+second. The
other patterns are forbidden by p!=r and q!=r. Their finite product's
three-label coefficient retains the complete source without imposing
separability or dropping coincidences. Show a uniform growing product
limit and the three weighted label limits; prove coincident labels vanish
after logarithmic normalization. Mertens first/second theorems in the
corpus supply prime logarithmic mass, but the moving test and product
limit still need proof. No numerical experiments are used.

Hard obligations: exact local identities; uniform summable remainder with
moving parameters; logarithmic prime measure convergence; actual labelled
product convergence; zeta-pole/cofactor transfer. A compact near-pole law
alone does NOT bound the full physical Mellin integral: frequencies of
order one and tails, contour transfer, signed axes cancellation, growing
moments/cofactors and common-height self-return remain open.

Status: PAPER CONJECTURE / NO LEAN THEOREM YET. Do not count algebraic
rewriting alone as completion of the growing-source problem.

Exact boundary discovered during symbolic expansion: with the second
Mellin variable balanced (y=z), the four local Euler offsets simplify to
E_0=(1-z)^(-2), E_-1=x E_0, E_-2=x^2 E_0,
E_1=-z/(x(1-z))*E_0. Thus first/second label collisions agree EXACTLY
with the product of their single-label responses on this boundary.
Writing a_p(s)=p^(1-s), the complete labelled term becomes its balanced
value times a_q(s)/a_r(s). The complete masked sum therefore becomes
  -A * sum_r b_r/a_r(s) * R_r * sum_(q!=r) w_q a_q(s).
This is a potentially decisive exact simplification of a full moving
cofactor boundary, not a factorization assumption on the physical profile.
Lean verification in progress. General two-moving-variable limit remains
the target; this identity supplies a boundary check and a tractable first
full-source limit. Full physical Mellin transfer remains open.

Paper proof of the proposed full joint limit (formalization outstanding):
fix a compact parameter set with Re(lambda),Re(mu)>0. For p<=N set
u=log p/log N, a=exp(-lambda u), b=exp(-mu u), z=1/p. Then a,b and
their inverses lie in a fixed compact annulus. The cofactor-completed local
base H=(1-za)(1-zb)E_0 has the exact identity
  H=1+(z F+z^2(a+b-2))/(1-z)^2,
  F=(a+b-a^2-b^2)/(ab).
The identity and the corresponding first-tag identity passed symbolic
Lean check9394; no numerical experiment. F equals the numerator of J at u.
For a fixed sufficiently large prime threshold, H is uniformly within
1/2 of 1. The finite head tends uniformly to 1 as N grows. Consequently
log H-zF is bounded by C/p^2 and tends to zero for each fixed prime.
Tannery yields a vanishing total remainder. The removable quotient F(u)/u
has value lambda+mu at zero (NOT zero). Mertens prime-window convergence
therefore gives product H -> exp J. Compact-uniform convergence follows
from joint continuity on the compact parameter/unit-interval set and a
finite-net argument for the uniformly bounded positive window measures.

For allowed tag patterns divide local responses by E_0. Their leading
values as z->0 are A=(a+b-1)/a, B=(a+b-1)/b,
C=1-1/a-1/b, and D=(a^2+b^2+ab-a-b)/(ab) for the coincident first two.
The exact rational expressions make the A/B/C errors O(1/p), uniformly
on that annulus after the same finite-head separation; D stays bounded.
Thus log-normalized weighted label sums converge to I_A/I_B/I_C.
Replacing the sum over three distinct labels by the product of the three
label sums costs O(L) from each pair collision times an O(L) remaining
sum, hence o(L^3); the exact allowed first+second collision also costs
o(L^3). Bounds use sum(log p)^2/p^2<infinity and bounded local responses.
All masks are retained in this comparison. Small-prime responses at the
balanced point are finite; C differs from -1 by O(1/p), already accounted
for by the summable weighted error.

Finally the exact completed source is A(P)^3*zeta(s)*zeta(t)*product(H)
times this complete labelled response sum. The corpus Mertens product
theorem gives A(P)*L->exp(-gamma); both pole-removed zeta factors tend to1.
This proves the stated limit on paper, assuming the displayed local
rational identities (first two checked, remaining tag identities still
to be Lean checked). This is NOT a completed Lean proof and not a proof
of the physical signed saving. The remaining formal work is substantial:
tag identities, actual finite-product coefficient assembly, uniform
complex prime-window/Tannery estimates, and the actual-source transfer.

01an verification update: scratch58299 verifies all four rational local
identities (base, first, third, coincident first+second) with empty Lean
output. The second single-tag identity follows by exchanging x,y; no
separate production theorem is claimed yet. Scratch14567 verifies the
complete one-balanced labelled and masked-row formulas and literal
prime-power/exponential ratio. A uniform vertical bound is now being
checked: norm of the whole one-balanced source at (1+i*tau,1) is at most
its balanced norm, with equality at tau=0. This retains all labels and
masks; it does not imply a saving as the prime cutoff grows.

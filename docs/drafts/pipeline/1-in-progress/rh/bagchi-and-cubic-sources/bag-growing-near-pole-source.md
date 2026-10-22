# BAG growing-prime near-pole source

Continuation01ap. POINTWISE FULL LABELLED LAW NOW LEAN AUDITED; compact-uniform
source law and physical transfer remain active. Hard target: the actual `criticalCompletedConeEuler`
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

Full labelled joint-limit status: POINTWISE THEOREM LEAN AUDITED in
ChiRamanujanGrowingLabeledSource; the earlier conjecture/history below is
retained. Compact-uniform statement remains unformalized.
The growing cofactors and complete unlabelled joint limit are now formalized
in ChiRamanujanMovingCofactorLimit and ChiRamanujanJointBaseLimit.
The exact local identities and complete one-balanced law are now audited
in P2/P3 bag-critical-mellin-deformation. Do not count these as completion
of the growing two-variable source problem.

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
Lean verification completed below. General two-moving-variable limit remains
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
rational identities (all four displayed local identities now Lean checked). This is NOT a completed Lean proof and not a proof
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

Final01an: production28970 empty PASS for the 306-line
ChiRamanujanCriticalMellinDeformation leaf (12 theorems, two definitions).
Axiom31311 all14 standard3 only. Index99071/API14/import once verified.
Lint19933:31 unrelated unreachable modules,174 warnings; global NOT clean.
All owned jobs terminal; scratch sources cleaned, logs/search JSON kept.
No full build, subagents, numerical experiments or limit hacks.

Search audit: deep full-transfer52345 nonpartial65861files,gen1243615;
critical-bound15461 nonpartial65861files,gen1243647; log-prime52808
nonpartial65861files,gen1243702; joint-log87066 nonpartial65863files,
gen1243740; moving-correction48423 nonpartial65866files,gen1243824.
All candidate/source entries and proposals inspected. All deep searches
report no errors, refresh incomplete/background indexer, source-only
candidates and coverage snapshots; generated proposals not accepted as
proofs. The weak prime-window and Mertens-product theorems were verified
in source after broad search and exhaustive relevant rg follow-ups.
Lexical70420 returned20 relevant hits, no deep candidate/source sections;
no one-balanced complete-source law found. Saved /tmp/bag-*-search-01an.json.

Useful existing inputs for the next hard proof: MertensPrimeWindowWeakConvergence
(tendsto_mertensPrimeWindow_div_log), MertensThirdTheorem
(tendsto_mertensPrimeProduct_mul_log), PrimeProfileWindowLimit
(tendsto_finsetSum_Icc_zero and product-log assembly), and
ChiRamanujanWeightedCubicTrace (normal convergence of cubicPrimeFactor
and continuity of cubicEulerCorrection). The latter tends to1 under
moving parameters near (1,0,0), so use it to remove the regular product
remainder rather than reproving a generic absolute-product estimate.
Caution: divProfile in PrimeProfileWindowLimit is extended by ZERO; our
F(u)/u instead has value lambda+mu at0 and needs the correct extension.

Assessment: exact full moving-boundary control advanced; full signed axes
saving and joint growing-source limit NOT solved. Next formalize the actual
joint limit, not additional boundary wrappers or constant refinements.
Afterward still prove transfer to the whole physical Mellin integral,
growing moments/cofactors and common-height self-return. RH remains open.

Continuation01ao hard subproblem: prove, for every complex u, the actual
finite Euler-product ratio at s=1-u/log N tends to exp(-P(u)), where
P(u)=integral_0^1 (exp(u t)-1)/t dt with its continuous value u at t=0.
Use u*dslope(exp,0,u*t) for that removable extension. Complex prime-window
convergence follows by real/imaginary parts of the corpus theorem. For the
local log remainder, the corpus radialNome bounds give |q|<=3/4 and
|q|^2<=p^(-3/2) once the moving drift is small. Thus the difference between
log(1-q), its linear term, and the balanced counterpart has a fixed
summable majorant and vanishes termwise. Complex Tannery and exp(sum log)
then prove the actual growing product law. This supplies the four Euler
ratios in H; the regular correction tends to1 by its existing normal
convergence. The complete labelled product remains the larger target.

01ao result: the actual growing Euler ratio and original coprime cofactor
limits are formalized in ChiRamanujanMovingCofactorLimit (441 lines,
eight public declarations). Production46118 empty PASS, axioms53987
standard three only. The actual cofactor itself tends to
-exp(-gamma-P(u))/u at s=1-u/log N for u in Complex units. This advances
the cofactor part; the complete joint labelled source is still open.
Next assemble the four Euler ratios with the normally convergent cubic
correction to prove the actual unlabelled joint factor, then retain all
labelled rows and collisions. Physical axes cancellation is not inferred.

01ao second conjecture/proof stage: the unlabelled complete product
H_N(lambda,mu) tends to exp(P(lambda)+P(mu)-P(lambda-mu)-P(mu-lambda)).
An exact local factorization rewrites it as the cubic normal correction
at (1,lambda/log N,mu/log N), times R_N(lambda-mu)R_N(mu-lambda) /
[R_N(lambda)R_N(mu)]. The actual cutoff is cofinal among finite prime sets;
local uniform convergence and continuity prove the moving regular product
limit1. All these steps have checked in scratch except a finite-product
cutoff annotation, now corrected. The current audit also attaches both
original coprime cofactors and the actual weightedTrace, with both moving
pole factors. Complete distinguished labels are still outstanding.

The exact next label assembly must retain all exclusions and p=q:
with a_p,b_p,c_p,d_p the four response/E0 ratios and w_p=log p/p,
T=sum_r w_r*c_r*((sum_(p!=r)w_p*a_p)*(sum_(q!=r)w_q*b_q)
  +sum_(p!=r)w_p^2*(d_p-a_p*b_p)).
The full source is A^3*product(E0)*T before attaching both cofactors.
This formula keeps the allowed collision explicitly. Its growing limit
needs the three actual response row limits, their uniform bounds and
summable collision control; it must not be replaced by independent labels.

Stronger proof organization for the remaining rows, grounded in the exact
local rational identities and Mertens prime-window weak limit: uniform
O(1/p) error estimates are sufficient but unnecessary. Write each response
as R(z,t), z=1/p, t=log p/log N. At z=0, the denominator H is1 and R(0,t)
is the proposed leading response. On the compact t interval, continuity
makes R(z,t)-R(0,t) uniformly small for sufficiently small z. The finite
prime head tends to its balanced values as N grows and contributes zero
after division by log N. This gives the actual row limits once all
rational denominators and finite-head continuity are proved. For collision
terms, bounded responses and w_p<=1 imply sum w_p^2<=sum w_p=O(log N),
so pair collisions cost O((log N)^2)=o((log N)^3). No sharp numerical
constant or stronger summability theorem is needed. This is a proof plan,
not yet a Lean theorem; the exact masked finite-product assembly remains
mandatory.

Final second-stage production87210 empty PASS: ChiRamanujanJointBaseLimit,
251 lines, two public theorems and one definition. The actual entire
unlabelled valuation trace with both growing original coprime cofactors
has the stated moving double-pole limit at every nonzero complex pair.
The product limit itself permits every complex pair, including zero
coordinates. Convergence is pointwise in fixed displacements; no
compact-uniform parameter result is claimed. Next work remains the
complete actual masked labelled source, followed by physical transfer.

Continuation01ap active conjecture: the full literal criticalWeightedConeEuler
admits exactly the masked response formula recorded above, with the allowed
p=q correction retained. Prove the equality by splitting distinct and
coincident first/second labels, factoring each local prime against E0, and
summing the exact collision difference. The previous joint-base limit gives
eventual nonvanishing of every local E0 at the actual growing Mellin points,
so the final moving-family identity has no extra hypothesis. Then establish
the actual response row limits and collision decay. No physical cancellation
will be inferred merely from this near-pole identity.

01ap conjecture correction exposed by Lean96436: the proposed unrestricted
triple-collision coefficient3 is FALSE; it is2. Exact expansion of T is
  Arow*Brow*Crow + Crow*sum w^2*(d-a*b)
  - Arow*sum w^2*b*c - Brow*sum w^2*a*c
  + sum w^3*c*(2*a*b-d).
The product of two exclusions supplies one a*b contribution; subtracting
the excluded pair correction supplies the second. There is no third.
Positive survivor: this corrected exact cluster decomposition, now under
audit, retains all pair/triple collisions and is the expression to bound.
No numerical test was used; symbolic Lean ring checking exposed the error.

Final masked assembly01ap: production22902 empty PASS, axioms85967 all10
standard three, index99430 PASS. New leaf ChiRamanujanMaskedMellinSource
294lines, four public theorems/six definitions. Full actual completed
moving source is exactly A^3*T times the entire unlabelled trace with
both cofactors. Corrected expansion coefficient2 is audited.

Concrete next analytic mechanism (current mathlib source checked):
IsCompact.eventually_forall_of_forall_eventually gives uniform-in-t
smallness of R(z,t)-R(0,t) as z->0 from continuity at (0,t), t in[0,1].
Compose with z=1/p to choose a fixed prime threshold. The finite head
R(1/p,logp/logN) tends to R(1/p,0) and its weight divided by logN vanishes.
The remaining weighted tail is at most epsilon times Mertens weight mass;
the existing mass/logN->1 closes the error. This needs only continuity on
the zero-z slice and at each fixed-prime balanced point, not global
continuity across rational-response poles. Then the corpus complex weak
prime-window limit identifies the three leading integrals. Build this
missing moving-profile theorem and apply it to the actual rational
responses. Do not stop at assuming row convergence.

Scratch73434 empty PASS: the complete moving-response window theorem is
now proved from the two continuity conditions, using the corpus complex
weak window and the separately proved vanishing error. This is still a
generic helper; actual rational-response instantiation is in progress.
The four profiles use the exact normalized numerator formulas from
CriticalMellinDeformation divided by H. H(0,a,b)=1 and H(z,1,1)=1, giving
precisely the zero-slice and fixed-prime-head continuity required. Need
formal continuity, actual-prime identities and leading-profile evaluation.

01ap stronger collision route, now being checked: w_p=logp/p is exactly
W(z)=-z*log z at z=1/p. W is continuous at0 with W(0)=0. Thus the SAME
moving-window theorem applies to W(z)*(d-a*b), W(z)*b*c, W(z)*a*c,
and W(z)^2*c*(2*a*b-d). Their zero-z slices vanish identically, so the
weighted pair/triple sums divided by logN tend to0. Combined with the
three row limits and 1/logN->0, every correction in T/(logN)^3 vanishes.
This avoids a separate uniform-response bound and rough collision-norm
estimate; the proof still retains every actual collision. Need verify
log-weight continuity API and actual profile identities in Lean.

Scratch64116 PASS: all FOUR actual response rows now have their explicit
leading-profile integrals. Scratch59931 PASS: all four exact collision
moments divided by logN tend to0, using W(z)=-z logz and the same moving
window theorem. No uniform norm-bound premise. Both scratch results had
only minor tactic warnings, now removed. Full original completed-source
limit is being assembled with the audited masked identity, Mertens
normalization and the original unlabelled two-cofactor moving trace.
The convergence proved so far is pointwise in fixed complex displacements;
no compact-uniform parameter or physical transfer claim.

Final01ap: full original labelled source law production88601 empty PASS;
MovingResponseWindow57016 and MovingLabelRows3369 empty PASS. Updated
MovingCofactorLimit95159 and MaskedMellinSource22902 also PASS. Axiom71945
all30 public declarations standard3 only. Index69878/API30/30/imports once.
Lint66470:23 unrelated unreachable modules,174 warnings; global NOT clean.
Pointwise for fixed nonzero complex pairs, not compact-uniform or a physical
saving. Next hard transfer conjecture/card: bag-moving-physical-mellin-lines.

# BAG uniform fractional compact multiplication

2026-10-06,01ax. Active after compact logarithmic fractional chart transfer.
Target: bound the complete directional fractional energy of A*f by physical
fractional energy and L2 mass, for compact C1 coefficients A; derive the
coefficient constants from compactness and differentiability, then make them
uniform for the actual compact Mellin-weight/cutoff/Euler family. No assumed
analytic budget in public conclusions. This is needed to turn the new
unweighted planar chart estimate into1<s<3/2 moving Mellin energy.

Corpus grounding: LocalLogFractionalEnergy closes scalar and planar chart
energies; DirectionalGagliardoFourier supplies exact directional spectral
identity; PositiveQuadrantMellinLines defines the exact weighted log function,
Euler operators and actual Schwartz gradient. Installed
ContDiff.lipschitzWith_of_hasCompactSupport derives a Lipschitz constant from
compact C1 data; HasCompactSupport.exists_bound_of_continuous derives the
supremum bound. These constants must be proved uniform for the compact
parameter family, not assumed uniform from pointwise Schwartz membership.

Conjecture/proof mechanism: expand A(x)f(x)-A(y)f(y) exactly as
 A(x)*(f(x)-f(y))+(A(x)-A(y))*f(y).
The squared first term costs bounded A times the physical energy. The second
term uses the Lipschitz increment for0<h<=1 and the supremum bound forh>1.
Its scalar majorant is L^2*|v|^2*h^(1-2s) on(0,1] and4*M^2*h^(-1-2s)
on(1,infinity); both are admitted for0<s<1. Nonnegative integration,
translation invariance, and the exact product decomposition then give the
full fractional multiplier theorem. Uniform compact parameter derivatives
will provide M,L for the actual cutoff coefficients. Apply to each exact
Euler derivative, with physical first derivatives retained.

Search54229 /tmp/bag-fractional-multiplier-search-01ax.json: partial because
local filter/judge returned malformed JSON;66794allindexed/noinventoryerrors,
index1255117,coverage1255132=current,semanticcoverageunmeasured. All20candidate
and20source statements plus proposed ingredient set inspected. LipschitzBound
product calculus and compact support multiplication are relevant primitive
mechanisms, not a completed fractional multiplier theorem. The retrieved
Gagliardo scalar scaling and newly indexed exact fractional near/far split
support the admitted integration step. Continue proof construction; no route
pivot due to the partial search or missing ready-made theorem.

2026-10-06 01ax compact parameter fractional multipliers CLOSED.
HTGeometry.FractionalCompactMultiplier269lines/API3: complete C1 multiplier
energy bound, uniform joint-parameter version, finite Schwartz spectral
corollary. Compactness and differentiability derive coefficient budgets.
Scratch64419/log05PASS; production26654emptyPASS; imported axioms29266standard3;
index17064PASS/API3/importonce; scoped diffcheckPASS. Lint49753terminal1:
15 unrelated unreachable,362warnings,noownedfinding; exactnames P2/P3
bag-compact-parameter-fractional-multipliers. Generic multiplier mechanism
closed; actual Mellin coefficient/Euler family remains the next obligation.
P1 bag-compact-mellin-coefficients and scratch /tmp/bag-compact-mellin-coefficients-01ax.lean
now construct literal compact parameter/physical cutoffs and the coefficient
eta(sigma)*chi(x)*exp(sum sigma_i log x_i). Smoothness uses positivity on
physical support and local zero extension off it; no assumed uniform norm.
Initial coefficient audit22339/log01 running. RH/open BAG endgame unchanged.

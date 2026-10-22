# Route L: complete integrand admission at the original divisor

- **ID:** L-C28
- **Date:** 2026-09-11
- **Stage:** 3-formalized; targeted build, complete axiom audit and global lint passed
- **Type:** THEOREM (paper and Lean)
- **Source:** [source-selected completion attack](../1-in-progress/route-l-source-selected-completion-attack.md), C28
- **Statement:** The original complete tensor remainder has a summable integrated-norm majorant after source-selected depth admission; its whole cutoff integral agrees with the actual cutoff reader and retains the normalized fixed-six top-jet response at every Xi divisor.
- **RH status:** unproved; fixed Sonin/Burnol agreement at the original horizontal anchor remains missing.

## Source and exact domain

Keep the original internally promoted Hilbert sources, their physical
`2*pi` coordinate scaling, forced half-density, and exact integer shell
`a=n+216`. Let `s(w)=1/2+i*w`, with `|Im(w)|,|Im(z)|<1` and
`Re(s(w)),Re(s(z))>0`. No zero-location information enters these domains.
The complete remainder is the tensor of the two full sources minus the
tensor of their leading parts; both cross terms and the double-tail term
remain. The leading Green component stays recorded separately.

For cutoff `M`, retain a column only when its literal depth `m` satisfies
`m>=M`, `1/m<Re(s(w))`, and `1/m<Re(s(z))`. Apply this predicate to the
original integrand before integration. Omitted columns are the zero
integrand. The existing eventual-admission theorem shows that, for every
sufficiently large `M`, this is exactly the original coordinate cutoff
`a>=6^M`, without further exclusions. At every Xi divisor its original
spectral point satisfies the required positive-real-part and strip laws.

## Dependency-closed paper proof

1. For the strict arithmetic term with label `p+j+1`, the corpus gives
   an exact translated Fourier--Laplace jet integrand. Its integrated
   norm is the modulus of its spectral coefficient times
   `I_k(w)=integral |theta-jet-integrand(k,w,x)| dx`. Translation changes
   neither that norm nor the measure; the physical `2*pi` factor cancels
   its Jacobian exactly.
2. Put `t_m(w)=sum_j |a_(p,m,w,j)|`. The complete coefficient estimate is
   `|a_(p,m,w,j)| <= r_p^(m*Re(s(w))-3/2) b_(p,j)` once
   `m*Re(s(w))>=3/2`, with `0<r_p=p/(p+1)<1` and summable `b`.
   Thus `t_m(w)` is summable in depth on every `Re(s(w))>0`.
   Applied only on admitted retained depths, Tonelli bounds the
   integrated norm of the full strict source by `I_k(w)*t_m(w)`.
   No cancellation of its arithmetic coefficients is used.
3. The exact Hilbert tensor decomposition gives the three contributions
   `H tensor U`, `T tensor J`, and `T tensor U`. Product-measure
   integration of each norm factors into the two integrated factor
   norms. Triangle control therefore bounds the complete depth-`m`
   remainder by
   `a_m^2 * I_k(w)*I_l(z) * [t_m(w)+t_m(z)+t_m(w)*t_m(z)]`.
   This is an estimate for the actual integrand, not just its integral.
4. The bracket is summable: both sequences are nonnegative and summable,
   and their pointwise product is summable. The exact shell has
   `5*6^m` coordinates, cancelling `a_m^2=6^(-m)` up to factor five.
   The original flattening lies between `1/6` and one. Consequently the
   sum over every original column of the integrated norm of its masked
   remainder is finite. Every divisibility restriction has the same
   majorant. The complete countable source sum is integrable and its
   integral equals the absolutely convergent sum of its column integrals.
5. On each retained column, the existing admitted Fourier--Laplace
   identity gives exactly `c*C_m/a`, where
   `c=XiC^(k)(w)*XiC^(l)(z)` and `C_m=M_6(m,w)*M_6(m,z)-1`.
   The leading tensor integral gives `c/a`. Subtracting that admitted
   leading component identifies this column with the diagonal of the
   original integral operator minus `c*Q`. Thus every sufficiently late
   cutoff has its actual operator/readout identification at the original
   spectral point. Unadmitted discarded integrals are not evaluated.
6. On the diagonal `z=w`, finite-shell regrouping at label six gives
   the same complete shell sum as C27. Its geometric moving-tail limit
   was already proved for every `Re(s(w))>0`, before the narrower
   operator-admission specialization. Hence the actual complete cutoff
   integral and second boundary coefficient satisfy
   `N_M*J_M -> 2*mu(successor(6))*c*(log(6))^2/[6*(1-q)]`,
   with C27's original normalizer and `q=N_1^(-1)`.
7. At any Xi divisor, multiplicity-top orders make `c` nonzero. All
   sufficiently late admitted cutoffs therefore retain a nonzero
   fixed-six second response. Adjacent lower/top internal orders give
   the zero/nonzero conormal pair. Every finite diagonal repair
   disappears after a sufficiently late cutoff and preserves the limit.

The norm and convergence assertions in steps 1--4 precede zero
specialization and justify the interchange in step 4 independently of
scalar cancellation. Steps 5--7 retain each divisor's original horizontal
anchor; reflection is not used to replace it by a different divisor.

## Scope

This closes source admission and a full-source measurement identity,
not the source-to-Sonin cyclic comparison. The regulator tends to zero
at each fixed cutoff first; the normalized source-depth limit follows.
No joint-limit interchange or cutoff-uniform regulator rate is claimed.
Critical top-jet sources also retain the response, so its vanishing is
not an RH condition. Finite diagonal support is not finite operator rank.

## Discovery and failed transfers

Three corpus searches attacked uncancelled translated norms, product-measure
tensor admission, and source-cutoff/diagonal transfer. All candidate statements
and source-method summaries were inspected (20 of each per search). Coverage
was partial: semantic `2196271/2336767`, pending generations `823339` and
`823340`, with runtime deadlines and worker disconnections; no proof ideas
or ingredient sets were returned. Direct source inspection supplied the
exact residual integrated norm, the physical-coordinate representative,
the three-term tensor decomposition, and the existing Tonelli theorem.
Compact-support, nuclear-tensor, and finite-shell search hits did not by
themselves justify the full source sum; the present uncancelled depth
majorant supplies that missing argument.

Broad arXiv searches used fragmentation, coercivity, sewing, tightness,
compactness, transport, reciprocity, renewal, balayage and cocycle, preferring
June--September 2026. The dated sewing results concern robotics and learned
correspondence. The opened [August 2026 fabric-alignment paper](https://arxiv.org/abs/2608.09528)
uses a geometric alignment procedure; it supplies no exact integral identity
or source-to-reader intertwining theorem applicable here. Other queries
returned older work or no hits. No external hypothesis is imported.

## Verification state

All 45 theorems passed `lake env lean /tmp/route_l_full_source_admission.lean`
with no errors or warnings. The checked development is in
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerGammaSixCompleteIntegrandAdmission.lean`
and wired into `RHTower`. The final targeted command
`lake build GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixCompleteIntegrandAdmission`
passed; the new module built in 112 seconds. No full umbrella build ran.

`lake env lean /tmp/route_l_complete_integrand_axioms.lean` audited all
45 theorem names against the source. Every result uses only `propext`,
`Classical.choice`, and `Quot.sound`; no added axiom or forbidden
declaration occurs. All C28 Lean processes completed.

The original global lint run reported two unrelated unreachable modules.
The subsequent C29 audit ran `scripts/formal_tools.py lint` successfully
with exit status zero and `formal lint passed`, clearing that final gate.
The 45-theorem source and its earlier targeted build and axiom audit
remain unchanged; this card is now formalized. No unconditional RH
theorem is claimed.

The successor is the audited [regulator--depth crossover](route-l-regulator-depth-crossover.md),
which keeps the actual regulator and normalizer together. Its joint
limit is proved in that separate module.

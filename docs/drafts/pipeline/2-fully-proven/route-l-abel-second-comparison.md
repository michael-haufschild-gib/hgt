# Route L: second boundary variation and complete diagonal recovery

- **ID:** L-C26
- **Date:** 2026-09-11
- **Stage:** 2-fully-proven; Lean checks complete, repository lint gate pending
- **Type:** THEOREM (Lean); 27 theorems checked
- **Module:** `GaloisForLFunctions.RHTower.DeningerGammaSixAbelSecondComparison`
- **Source:** [source-selected completion attack](../1-in-progress/route-l-source-selected-completion-attack.md), C26
- **Statement:** The actual second boundary discrepancy reads the complete summable correction through divisibility sums; these measurements and the scalar first variation determine every diagonal correction coefficient. A finite diagonal repair cannot remove the discrepancy at every ordinary dilation from an admitted multiplicity-top source.
- **RH status:** unproved; source-to-fixed-physical-reader agreement remains open.

## Exact source and comparison

Use the same complete integral operator as
[C24](../3-formalized/route-l-integral-column-law.md) and the admitted Abel path from
[C25](../3-formalized/route-l-critical-abel-reader.md). Write its diagonal as
`T_kk=c/k+r_k`, with `sum_k |r_k|<infinity`. Here
`c=XiC^(a)(w)*XiC^(b)(z)`, and the complete correction includes the
omitted finite head. The actual every-depth source domain is
`|Im(w)|,|Im(z)|<1`, `Re(s(w)),Re(s(z))>1/3`, where `s(w)=1/2+i*w`.

For positive `epsilon`, the literal admitted quantities are

`Z_epsilon = sum_(k>=1) k^(-1-epsilon)`,
`A_epsilon(T) = Z_epsilon^(-1)*sum_(k>=1) k^(-epsilon)*T_kk`,
`D_epsilon(n,T) = A_epsilon(S_n^* T S_n)-A_epsilon(T P_n)`.

`P_n` is the original ordinary-integer divisibility projection. The
already fixed physical BV boundary on this path is
`B_n((1+epsilon)/2)=(1/n)*(1-n^(-epsilon))`.

The new limits, before divisor specialization, are

1. `(A_epsilon(T)-c)/epsilon -> sum_k r_k`;
2. `[D_epsilon(n,T)-c*B_n((1+epsilon)/2)]/epsilon^2
   -> log(n)*sum_(n divides k) r_k`.

The second expression is a normalized discrepancy coefficient, not a
claim that a second derivative exists or that its value lacks a factor
of two. No differentiability of the complete correction is assumed.

## Dependency-closed paper proof

1. The exact Gibbs weight is `k^(-epsilon)`. For positive `epsilon`,
   `|k^(-epsilon)*r_k|<=|r_k|`, and each term tends to `r_k`.
   Filter-level Tannery therefore gives
   `sum_k k^(-epsilon)*r_k -> sum_k r_k`. The source theorem supplies
   absolute summability. This also applies after every divisibility
   projection, since an indicator preserves summability.
2. C25 proves `epsilon*Z_epsilon->1`. Thus
   `A_epsilon(R)/epsilon -> sum_k r_k`, including for `R P_n`.
   The admitted reader is linear and reads the reciprocal Green
   operator `Q` as one, giving the first limit above.
3. The original operator identities give the exact principal equality
   `D_epsilon(n,Q)=B_n((1+epsilon)/2)`. Domain closure under subtraction,
   scalar multiplication, compression and projection yields
   `D_epsilon(n,T)-c*B_n=D_epsilon(n,R)`.
4. The exact weighted exchange law is
   `D_epsilon(n,R)=(n^epsilon-1)*A_epsilon(R P_n)`.
   Divide both factors by `epsilon`. C25 supplies
   `(n^epsilon-1)/epsilon->log(n)`; step 2 supplies the other limit.
   Their product proves the second coefficient formula.
5. For `n>1`, `log(n)` is nonzero. All second coefficients vanish
   precisely when all nontrivial multiples sums of `r` vanish. The
   existing absolutely summable divisibility reconstruction theorem
   makes this equivalent to `r` being supported at the unit. Conversely,
   a unit-supported correction gives zero at every such boundary.
6. If two summable corrections have the same second coefficients and
   the same scalar first variation, they have equal multiples sums at
   every positive integer: the scalar variation supplies the missing
   value at one. Existing divisibility-sum injectivity then gives equality
   of the entire diagonal correction. This recovers no off-diagonal
   operator entry, and requires all ordinary dilation labels.
7. For the actual integral operator, the omitted coordinate two has
   correction `-c/2`. Unit support forces `c=0`. Conversely, C24 proves
   that `c=0` makes the whole literal integral operator zero. Therefore
   second-order agreement at every ordinary `n>1` holds exactly when
   `c=0` for this unrepaired placement.
8. The obstruction is stronger than this omitted-head argument. The
   correction at coordinate `a=n+216` is exactly the full integral
   remainder. Its complete Fourier--Laplace identity is
   `d_n*a_m^2*(M_6(m,w)^2-1)*c`, where `m` is the shell depth.
   Both `d_n` and `a_m` are strictly positive. C23 proves the complete
   diagonal multiplier eventually nonzero whenever `Re(s(w))>0`.
   Taking `n=6^m` realizes each sufficiently large shell depth exactly.
   Hence, when `c!=0`, nonzero actual correction coefficients occur
   above every finite coordinate bound.
9. Any operator `F` with finite diagonal support vanishes at a
   sufficiently late such coordinate. Thus `T+F-c*Q` retains a nonunit
   correction. Its diagonal remains summable, so steps 4--5 imply a
   nonzero second coefficient at some ordinary `n>1`. At a divisor with
   `Re(rho)>1/3`, multiplicity-top orders give
   `c=[XiC^(q)(w_rho)]^2!=0` by the existing multiplicity theorem. The
   second-order agreement limit fails for some dilation after every
   finite diagonal repair. All source-domain and nonvanishing inputs
   are discharged by the actual source; no RH or comparison premise
   is introduced.

## No-go closure and positive survivor

**Rejected strengthening:** extending C25's first-order agreement to
second-order agreement at every ordinary dilation for the full top-jet
source, even after any finite diagonal correction.

**Strongest positive survivor:** exact second discrepancy, full diagonal
reconstruction from measured variations, sharp unit-support kernel, and
actual tail survival beyond every finite repair. These are properties
of the same complete source and reader, not a replacement zero reader.

This is not a prime-only reconstruction theorem. Neither a fixed
detecting prime nor the label six is specified by the existential
obstruction. Finite diagonal support is not the same as finite operator
rank. The regulator remains independent of the original spectral
parameter. The result neither constructs Sonin transport nor proves
all-prime source-action intertwining or reader agreement at
`tau=Re(rho)`. Critical top-jet sources also have this second-order
obstruction; demanding its absence would be an invalid RH condition.

## Searches and method audit

Deep and method searches covered second boundary variation, normalized
correction traces, Tannery limits, and multiples-sum injectivity. They
reported `partial=true`, pending generation `823332`, and semantic
coverage `2196271/2336631`. Local Qdrant and reranking deadlines limited
retrieval; no server was started. Candidate lemmas and source arguments
were inspected. Lexical fallback and direct current-source reads located
the applicable Tannery, actual Gibbs-domain, source-tail, and diagonal
reconstruction theorems. No claim of exhaustive fresh index coverage is
made; the exact applied names are checked by Lean.

Broad arXiv terms included `tomography`, `memory`, `scattering`,
`resolvent`, and `renewal`, with June--September 2026 preference.
The [September scattering preprint](https://arxiv.org/abs/2609.10504)
tests a proposed event mechanism against the accompanying recoil
spectrum and existing constraints; it supplies no arithmetic comparison
identity. The older [resolvent paper](https://arxiv.org/html/1912.10507v3)
relates Abel ergodicity to boundedness and a fixed-point/range
decomposition. No such source operator or physical identification is
constructed here, so that theorem cannot supply the missing comparison.

The [September range-renewal paper](https://arxiv.org/html/2609.05290v1),
Section 5.2, obtains local information from geometric sums using explicit
domination. Its positivity and regular-variation assumptions are not
available for the complex arithmetic correction. The useful next test
is instead to derive the actual complex shell sum and its own geometric
majorant, retaining the fixed dilation label. No paper is used as an RH
premise.

## Verification

All 27 theorems passed without warnings in
`lake env lean /tmp/route_l_abel_second_order.lean`.
`lake build GaloisForLFunctions.RHTower.DeningerGammaSixAbelSecondComparison`
passed (154 seconds for the new module). All 27 theorem axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`.
The Route L module is wired into `RHTower.lean`; whitespace checks passed.
No numerical experiment, full build or umbrella build was used.
All owned Lean processes completed.

The latest `scripts/formal_tools.py lint` exited with status 1 because
five unrelated concurrently added modules are unreachable from their
umbrellas: `RHTower.EulerDeletionCoprimeJointProduct`,
`RHTower.EulerDeletionCoprimePolygonSignature`,
`HTGeometry.WeightedMinimax.Alternation`,
`HTGeometry.WeightedMinimax.Coefficient`, and
`HTGeometry.WeightedMinimax.PolyRoots`. Earlier reported missing
imports were wired by their owners; these are the current gate errors.
No Route L lint error was reported. This card remains at stage 2 until the authoritative
repository gate passes; the target build and kernel axiom audit above
are complete. The unrelated modules have not been modified by this task.

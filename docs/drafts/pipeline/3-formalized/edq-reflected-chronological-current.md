# EDQ reflected chronological variation current

Stage: 3-formalized; dependency-closed paper proof and Lean verified.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH.
RH status: the current below supplies a source equation and a finite-prefix error certificate; its required location-separating sign is unproved.

Use actual successor labels p,q, so the literal moduli are p+1,q+1. Write r(s)=1-conjugate(s),
k_s(n)=(n+1)^(-s), P_p(s,N)=sum_(n<N) a_(p+1)(n+1)*k_s(n), and b_q(N)=N mod(q+1).
Let C_pq(s,N) be the actual chronological cross prefix with inner exponent s and outer exponent r(s).
Define the literal Abel remainder and terminal term by

`R_pq(s,n)=P_p(s,n+1)*conjugate(k_r(s)(n+1)-k_r(s)(n))*b_q(n+1)`,
`T_pq(s,N)=P_p(s,N-1)*conjugate(k_r(s)(N-1))*b_q(N)`.

Finite summation by parts gives

`C_pq(s,N)=T_pq(s,N)-sum_(n<N-1)[a_(p+1)(n+1)*b_q(n+1)/(n+1)+R_pq(s,n)]`.

The first summand is independent of s, including for shared factors. Therefore for any two
parameters s,t the entire arithmetic diagonal cancels exactly:

`C_pq(s,N)-C_pq(t,N)=T_pq(s,N)-T_pq(t,N)-sum_(n<N-1)(R_pq(s,n)-R_pq(t,n))`.

In the open critical strip, existing inner-prefix boundedness and summable kernel variation
prove that R_pq(s,.) is absolutely summable and T_pq(s,N) tends to zero. Thus every such
difference converges to the negative of an explicit absolutely summable source current, with
no coprimality or zero premise. No individual divergent limit has been subtracted.

For equal labels and t=r(s), the imaginary part of the finite cross difference is the imaginary
part of the full reflected endpoint product: the exact Gram bracket is real. At every actual
nontrivial zero this endpoint product tends to zero, so the current has zero imaginary part.
More precisely, for `J_p(s)=sum_n(R_pp(s,n)-R_pp(r(s),n))` and the actual deletion
endpoint D_p(s), the whole strip satisfies
`Im(J_p(s))=-Im(D_p(s)*conjugate(D_p(r(s))))`.
Reflection reverses the full complex current, and it vanishes identically on the critical line.
The new remaining comparison is nonvanishing of this imaginary current at an off-line zero,
or another independently justified restriction on its full complex value.

At an actual zero rho, the source prefix bound is
`norm(P_p(rho,n+1)) <= A_p(rho)*(n+2)^(-Re(rho))`,
where `A_p(rho)=2*p*(1+norm(rho)/Re(rho))` is the corpus's explicit Abel-tail constant. The derivative-scale kernel estimate
and Re(r(rho))=1-Re(rho) give
`norm(R_pq(rho,n)) <= K_pq(rho)/(n+1)^2`,
with `K_pq(rho)=A_p(rho)*q*norm(r(rho))`. The same holds for the actual reflected zero.
Since `1/x^2 <= 2*(1/x-1/(x+1))` for x>=1, a tail starting at N is at most
`2*K_pq(rho)/(N+1)`. The reflected current tail is at most the sum of the two bounds. Its
zero imaginary limit therefore supplies an explicit inverse-linear bound on every finite
imaginary current prefix. This is a symbolic all-cutoff theorem; no numerical certificate is used.

Corpus inputs: EulerDeletionCoprimeCrossCompletion, EulerDeletionQuasiShuffleCrossDomain,
EulerDeletionReflectedLogarithmicGram, EulerDeletionQuasiShuffleSecondConvergence,
DirichletAbel, DirichletKernelEstimate, DirichletFirstDifference, GaussianZetaGeometry.
The ordered theta-Mellin pair signature was also inspected; its indefinite pair kernel does
not supply the missing sign.


## Formal certificate

Leaf: `formal/GaloisForLFunctions/RHTower/EulerDeletionReflectedChronologicalCurrent.lean`
(318 lines; 15 public theorems, six public definitions, four private lemmas).
Namespace: `RHTower.DeletionReflectedCurrent`.

- `kernel_reflected_pair`, `reflectedCross_abel`, `reflectedCross_sub`: exact scalar reflection, complete finite Abel decomposition, and cancellation before limits.
- `abelRemainder_summable_norm`, `terminal_tendsto`, `variationCurrent_tendsto`: absolute source convergence and the actual difference limit throughout the open strip, without coprimality.
- `partner_partner`, `reflectionCurrent_partner`, `reflectionCurrent_of_re_half`: the reflection involution, full current antisymmetry, and critical-line vanishing.
- `reflectionCurrent_im`, `reflectionCurrent_im_at_nontrivial_zero`: full endpoint-product identification and unconditional zero imaginary part at every actual nontrivial zero.
- `norm_abelRemainder_at_nontrivial_zero`, `abelRemainder_tail_at_nontrivial_zero`: explicit inverse-square majorant and inverse-linear single-source tail.
- `variationCurrent_tail_at_nontrivial_zero`, `imaginary_prefix_bound_at_nontrivial_zero`: both reflected tails retained in the complete complex error and every finite imaginary-prefix constraint.

Final scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_current.lean`, exit 0, no diagnostics.
Final leaf audit: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionReflectedChronologicalCurrent`, exit 0. Only the new leaf rebuilt (4.9 seconds); dependencies cached/replayed. Umbrella import added; no full or umbrella build.
New-only axiom audit: `lake env lean /tmp/edq_current_axioms.lean`, exit 0. All 21 public declarations use only `propext`, `Classical.choice`, and `Quot.sound`; private lemmas are covered by their dependency closure. No added axioms, admissions, numerical premises, or external computation certificates.

Repository `scripts/formal_tools.py lint` ran once and passed, with existing file-size warnings.
The search index was refreshed once. Owned scratch Lean sources were removed after verification;
logs remain in `/tmp/edq_current.api.log`, `.check.log`, `.build.log`, `.axioms.log`, `.lint.log`,
and `.index.log`. Scoped whitespace, wiring, link, and owned-process checks passed.

RH remains unproved and unfalsified. The current and its quantitative certificate are available
for a source comparison; no nonvanishing or orientation law excluding off-line zeros is proved.
No route is retired.

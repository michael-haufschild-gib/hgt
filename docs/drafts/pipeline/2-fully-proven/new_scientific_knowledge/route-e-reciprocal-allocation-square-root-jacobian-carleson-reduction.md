# Route E reciprocal-allocation square-root Jacobian Carleson reduction

- **ID:** ROUTE-E-RECIPROCAL-ALLOCATION-JACOBIAN-001
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / WEIGHTED PHYSICAL KERNEL / CARLESON REDUCTION
- **Parent:** route-e-parity-coalesced-full-mass-reservoir-cube-law.md
- **Source:** OPEN-SOURCE-001
- **RH used:** no
- **Computation used:** no
- **Lean status:** exact finite reciprocal-allocation core is formalized in
  `RHTower/MobiusReciprocalAllocationJacobian.lean`: positive harmonic normalizer, nonnegative
  kernel, exact row stochasticity after physical projection, square-root Jacobian cancellation,
  unique neutral tilt `lambda=1`, and average-column capacity. The stretched-`L` asymptotic column
  estimate `(4)` and co-moving flux remain paper-only.

## 1. Result

Let \({\cal R}^{\rm coal}_X\) be parity-coalesced full-mass relation.  For anchor \(n\), write
\({\cal A}(n)\) for ordered admissible reservoir allocations.  If
\(\rho\in{\cal A}(n)\), let

\[
 T(\rho)=\prod_{G}\prod_{p\in R_G}p                    \tag{1}
\]

and let \({\cal V}(n,\rho)\) be set of distinct physical full terminals obtained from that
allocation and all admissible sequential \(E_3\) choices.  Put

\[
 N(n,\rho)=\#{\cal V}(n,\rho),\qquad
 H(n)=\sum_{\rho\in{\cal A}(n)}\frac1{T(\rho)}.          \tag{2}
\]

Define physical kernel, with repeated allocation representations of same terminal added, by

\[
 P_X^{\rm har}(n,v)
 =\sum_{\substack{\rho\in{\cal A}(n)\\v\in{\cal V}(n,\rho)}}
   \frac1{H(n)\,T(\rho)\,N(n,\rho)}.                    \tag{3}
\]

Then:

1. rows are exactly stochastic;
2. support is source-predeclared, opposite-Möbius-sign, co-moving, and moving-seam compatible;
3. uniformly on every extended physical interval,
   \[
   \boxed{
   \sup_v\sum_nP_X^{\rm har}(n,v)
   \le \exp\!\bigl(C(\log\log X)^{3/2}\bigr)}
   \tag{4}
   \]
   for one absolute \(C\) and all large \(X\);
4. every factor \(T(\rho)^{1/2}\) from physical inverse intervals cancels exactly against edge
   weight in (3).

Thus current \(X^{o(1)}\) Carleson loss can be made explicit and independent of reservoir-product
scale:

\[
 X^{O(1/L)}
 \quad\hbox{is removed, leaving}\quad
 \exp(O(L^{3/2})),\qquad L=\log\log X.                  \tag{5}
\]

This does not prove unit load \(1+o(1)\), but it removes largest known subpower source from
column estimate.  Remaining loss comes from structured-\(E_3\) density, inverse-window logarithms,
and physical support assignments—not reservoir magnitude.

## 2. Exact row normalization

Every \({\cal V}(n,\rho)\) is nonempty for large \(X\).  Summing (3) over physical terminals,
and retaining repeated allocation representations in inner sum, gives

\[
\begin{aligned}
 \sum_vP_X^{\rm har}(n,v)
 &=\sum_{\rho\in{\cal A}(n)}
   \sum_{v\in{\cal V}(n,\rho)}
   \frac1{H(n)T(\rho)N(n,\rho)}\\
 &=\frac1{H(n)}
   \sum_{\rho\in{\cal A}(n)}\frac1{T(\rho)}
 =1.                                                    \tag{6}
\end{aligned}
\]

Projection from labeled allocations to ordinary integers loses no row mass because coincident
representations are added, not discarded.

Existing exact ordered-allocation identity gives, if \(B=\sum_Gb_G\),

\[
 H(n)
 =\frac{B!}{\prod_Gb_G!}
   e_B\!\left((1/p)_{p\in{\cal P}_X\setminus\operatorname{supp}(n)}\right)
 =\frac{S({\cal P}_X)^B}{\prod_Gb_G!}(1+o(1)),          \tag{7}
\]

uniformly over central \(n\).  Since \(S({\cal P}_X)\sim L\) and every
\(b_G\le2\sqrt L\), (7) also gives

\[
 H(n)\ge1                                               \tag{8}
\]

for all large \(X\).  Only this weak consequence is needed for (4); full factorial gain in
(7) remains available for a sharper collision theorem.

## 3. Explicit row-token scale

At group \(G\), sparse-forbidden theorem gives at least

\[
 c\,\frac{\sqrt{U_G/t_G}}
 {(\log(U_G/t_G))^{0.45}\log\log(U_G/t_G)}              \tag{9}
\]

admissible sequential tokens, with a uniform \(c>0\).  There are at most \(3\sqrt L\) groups.
Using \(Y\le U_G/t_G\le2X\), quotienting possible labeled factorizations of same physical
terminal, and absorbing \(c^{3\sqrt L}\), one obtains explicit bound

\[
 \boxed{
 N(n,\rho)\ge
 \sqrt{\frac{n}{aT(\rho)}}\,
 \exp(-C_1L^{3/2}).}
 \tag{10}
\]

Indeed, product of all logarithmic losses in (9) has logarithm at most

\[
 0.45(3\sqrt L)L+O(\sqrt L\log L)=O(L^{3/2}),           \tag{11}
\]

and all physical factor-assignment multiplicities contribute only
\(\exp(O(L\log L))\).

Equation (10) turns one edge weight in (3) into

\[
 \frac1{H(n)T(\rho)N(n,\rho)}
 \le
 \frac{\exp(C_1L^{3/2})}{H(n)\sqrt{T(\rho)}}
 \sqrt{\frac an}.                                       \tag{12}
\]

This is critical square-root weight.

## 4. Exact cancellation of inverse Jacobian

Fix physical terminal \(v\), one structural assignment of its prime factors to \(a\), terminal
groups, and reservoir sets, and hence fixed \(T=T(\rho)\).  Inverting token interval gives at most

\[
 \boxed{
 \sqrt{\frac{vT}{a}}\,
 \exp(C_2L^{3/2})}
 \tag{13}
\]

source anchors for that structure.  Product of (12) and (13) is

\[
 \frac{\exp((C_1+C_2)L^{3/2})}{H(n)}
 \sqrt{\frac vn}.                                       \tag{14}
\]

Reservoir product has disappeared.  Co-moving law gives \(v/n=1+o(1)\), while (8) gives
\(H(n)\ge1\).  A terminal has \(O(L)\) prime factors.  Number of structural assignments to
\(a\), at most \(3\sqrt L\) groups, structured factors, and merged-source split is

\[
 \exp(O(L\log L)).                                      \tag{15}
\]

Summing (14) over (15) proves (4).

This proof bounds labeled incoming representations.  Physical quotient can only decrease column
load.

## 5. Uniqueness of reciprocal allocation exponent

Let allocation mass be proportional to \(T^{-\lambda}\), and condition uniformly on physical
terminals of that allocation.  Square-root row law (10) is

\[
 N(n,\rho)\asymp_{\rm subexp}T^{-1/2}.                  \tag{16}
\]

Hence one edge has \(T\)-exponent

\[
 T^{-\lambda}/N(n,\rho)
 \asymp_{\rm subexp}T^{1/2-\lambda}.                    \tag{17}
\]

Inverse source multiplicity (13) has exponent \(T^{1/2}\).  Column contribution therefore has
exponent

\[
 T^{1-\lambda}.                                        \tag{18}
\]

It is independent of reservoir magnitude exactly when

\[
 \boxed{\lambda=1.}                                    \tag{19}
\]

Thus allocation mass \(1/T\), equivalently per-edge square-root weight \(1/\sqrt T\), is unique
critical tilt.  For \(\lambda<1\), largest reservoirs are amplified.  For \(\lambda>1\), row mass
concentrates on smallest reservoirs and abandons harmonic allocation law which passes physical
pool-capacity gate.  Equation (19) is forced by matching forward token Jacobian
\(T^{-1/2}\) with inverse physical Jacobian \(T^{1/2}\).

## 6. Conjecture--proof--failure loops

### Loop A: uniform physical row kernel is canonical

[CONJECTURE] Equal mass on all physical terminals is optimal because row degrees have same
half-density exponent.

[FALSIFIED] It retains allocation-dependent inverse factor \(T^{1/2}\).  Reciprocal allocation
law (3) cancels it exactly and improves explicit loss from possible
\(X^{O(1/L)}\) to \(\exp(O(L^{3/2}))\).

### Loop B: weight allocations by \(T^{-\lambda}\) with tunable exponent

[CONJECTURE] Some off-critical exponent can trade row entropy for smaller column load.

[FAILED] Equation (18) leaves power \(T^{1-\lambda}\).  Only \(\lambda=1\) removes reservoir
scale.  Larger \(\lambda\) also destroys use of critical harmonic breadth by concentrating on
lowest products.

### Loop C: reciprocal weighting proves unit Carleson

[CONJECTURE] Exact square-root cancellation makes column load \(1+o(1)\).

[FAILED] Current all-interval \(E_3\) lower bound loses
\((\log y)^{0.45}\log\log y\) per group, inverse interval pays
\((\log y)^{1.55}\), and structural assignments remain.  Rigorous output is (4), not unit.

## 7. Revised open core

Use \(P_X^{\rm har}\), not uniform row kernel, in fixed-relation branch.  Remaining theorem is

HARMONIC-SQUARE-ROOT-UNIT-CARLESON-AND-COMOVING-FLUX:

\[
 \sup_v\sum_nP_X^{\rm har}(n,v)\le1+o(1)                \tag{20}
\]

interval-uniformly outside \(X^{1/2+o(1)}\) Gibbs budget, with same kernel reproducing normalized
friable/one-large-prime flux.  Equation (4) proves all reservoir-magnitude dependence has
already canceled.  Any further proof must use fine structured-token anti-concentration,
factorial normalization (7), or new physical incidence geometry.

## 8. Scientific and formal status

[PAPER-PROVED] [NOVELTY UNVERIFIED].  Inputs are existing sparse-forbidden \(E_3\) count,
physical inverse-interval count, co-moving law, and exact harmonic allocation identity.  New
content is kernel (3), explicit stretched-\(L\) column estimate (4), and critical-tilt
uniqueness (19).  No external literature search was performed under current instruction.  No
Lean was written or built while corpus refactor is active.

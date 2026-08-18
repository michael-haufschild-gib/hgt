# G-CE finite self-adjoint boundary transport

- **ID:** `g-ce-finite-self-adjoint-boundary-transport`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (Lean)
- **Routes:** Route G, G-exterior, G-CE, CCM
- **Date:** 2026-08-18
- **RH used:** no
- **Computation used:** no
- **Scientific status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`
  `[CANDIDATE NEW SOURCE-TRANSPORT LAW] [EXTERNAL PRIORITY UNVERIFIED] [NOT RH]`

## 1. Corpus-first frontier

Corpus already contains Suzuki's literal interval Friedrichs operator `A_a`, its exact restricted
Weil form, compact resolvent, ground eigenstate, form Hilbert space `H(T_a)`, and deficiency indices
`(1,1)`. It also contains abstract nested-aperture phase-locking and compact-core strong-resolvent
theorems. Rebuilding those results would not move frontier.

Missing source theorem was different: actual Gamma--Xi coupled-error columns had no positive finite
self-adjoint realization whose completion cost was controlled through growing canonical heads. In
particular, generic positivity could hide completed Xi error in an arbitrary bottom-right cap and
therefore destroy prime--polar--Gamma cancellation at boundary.

Preceding singular-graph wall theorem identifies exact unavoidable completion cost

\[
  G=4+|d|^2,
  \qquad d=\mathcal W_\Xi^{\rm anti}(1/2),
\]

but left source-native cofinal transport open.

## 2. Frozen conjecture

For canonical growing Hardy heads, take Schur-complement minimum rather than arbitrary positive
completion. Then one source-depth schedule should simultaneously transport:

1. complete finite boundary columns;
2. resulting finite positive self-adjoint operators in operator norm;
3. minimum completion budgets to exact singular graph energy `G`.

Falsifiers were:

1. singular Cauchy Gram matrices on canonical grids;
2. target minimum budget strictly below `G` in growing-head limit;
3. failure to synchronize source convergence over moving head dimension;
4. synchronization that preserves scalar budget but loses boundary column or operator;
5. any RH or abstract source-convergence premise entering proof.

None occurs.

## 3. Canonical minimum finite realization

For positive-definite `K in M_n(C)` and response column `b in C^n`, write `B_i=conj(b_i)` and

\[
 C(K,b)=
 \begin{pmatrix}
   K&B\\ B^*&B^*K^{-1}B
 \end{pmatrix},
 \qquad
 q(K,b)=\operatorname{Re}(B^*K^{-1}B).
\]

Schur complementation gives

\[
  C(K,b)\succeq0.
\]

Moreover, if

\[
 \begin{pmatrix}K&B\\B^*&q\end{pmatrix}\succeq0,
\]

then `q(K,b) <= q`. Thus `q(K,b)` is exact least scalar completion cost. Hermiticity of
`C(K,b)` makes its Euclidean continuous-linear-map realization self-adjoint.

This minimum principle is important: no positive cap can absorb source defect without paying its
measured Hardy interpolation energy.

## 4. Actual Gamma--Xi heads

At head size `N+2`, define

\[
 u_{N,i}=\frac{i}{N+1},\qquad 0\le i\le N+1,
\]

and Cauchy Gram

\[
 K_N(i,k)=\frac1{1+u_{N,k}+u_{N,i}}.
\]

Distinct right-half-plane nodes make `K_N` positive definite. Target response is

\[
 b_N(i)=s(u_{N,i})+d\,m(u_{N,i}),
 \quad s(u)=\frac{2u}{(1+u)^2},\quad m(u)=\frac1{1+u}.
\]

Actual source response at source depth `j` is

\[
 b_{j,N}(i)=s(u_{N,i})+
 D_{\sigma_j}(u_{N,i}),
\]

where `D_sigma` is corpus's clock-normalized true Gamma--Xi complement defect and
`sigma_j -> 1/2` is canonical critical source sequence. For each fixed `N` and every head node,

\[
 b_{j,N}(i)\longrightarrow b_N(i).
\]

Finite-dimensional continuity therefore gives fixed-head convergence of minimum completions,
Euclidean operators, and completion budgets.

## 5. Exact growing-head budget

Let `q_N=q(K_N,b_N)`. Global singular graph wall supplies upper bound

\[
 q_N\le G.
\]

Every canonical grid contains first two nodes

\[
 0,\qquad t_N=(N+1)^{-1}.
\]

Compressing positive minimum completion to those nodes and applying exact two-node saturation
formula gives

\[
 G-r_N\le q_N,
\]

where

\[
 r_N=
 \frac{8t_N^2(2t_N+3)}{(1+t_N)^2(1+2t_N)}\longrightarrow0.
\]

Hence squeeze theorem yields

\[
 q_N\longrightarrow 4+|d|^2.
\]

This is exact boundary-energy recovery: canonical finite heads see all singular graph debt.

## 6. One common cofinal source schedule

For fixed `(j,N)`, combine all required discrepancies into one nonnegative error

\[
 E(j,N)=
 \|A_{j,N}-A_N\|+
 |q(K_N,b_{j,N})-q_N|+
 \sum_{i=0}^{N+1}|b_{j,N}(i)-b_N(i)|.
\]

For every fixed `N`, `E(j,N) -> 0` as `j -> infinity`. Choose threshold `M_N` after which

\[
 E(j,N)\le t_N.
\]

Define

\[
 J_N=N+\sum_{k=0}^N M_k.
\]

Then `J_N` is strictly increasing, `J_N >= M_N`, and `E(J_N,N) <= t_N -> 0`. Therefore, along
one literal source schedule:

\[
 \|A_{J_N,N}-A_N\|\longrightarrow0,
\]

\[
 \sum_i|b_{J_N,N}(i)-b_N(i)|\longrightarrow0,
\]

and for every moving node choice `i_N`,

\[
 |b_{J_N,N}(i_N)-b_N(i_N)|\longrightarrow0.
\]

Finally,

\[
 q(K_N,b_{J_N,N})
 =\big(q(K_N,b_{J_N,N})-q_N\big)+q_N
 \longrightarrow 4+|d|^2.
\]

All source and target completions are positive semidefinite and all associated finite Euclidean
operators are self-adjoint.

## 7. Scientific consequence and limit

This closes G-CE's finite realization, positivity, convergence, and boundary-column transport
problem in singular graph coordinates. Transport is source-native and preserves completed
Gamma--Xi debt exactly; it neither assumes RH nor silently replaces actual source columns by a
generic convergent family.

Result does **not** prove RH. Since corpus already proves `|d|^2=0 iff RH`, remaining RH-bearing
problem is cancellation or exclusion of this exact debt in uncompleted physical coordinates. Nor
does theorem claim literal Suzuki interval operators converge across apertures: that separate
operator family already has formal abstract convergence reducers, while source occupancy/weight
selection remains distinct.

## 8. Literature audit

Suzuki's finite-interval construction supplies source-exact lower-bounded self-adjoint operators
but leaves cofinal source convergence unresolved. Connes--Consani--Moscovici finite self-adjoint
models and numerical convergence do not provide this Gamma--Xi minimum-completion law, exact
growing-head graph budget, or single-schedule whole-column transport.

No external priority claim is made pending specialist review.

## 9. Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/MobiusGammaXiCoupledErrorFiniteSelfAdjointBoundaryTransport.lean`

Core declarations:

- `finiteHardyMinimumCompletion_pos`
- `finiteHardyMinimumBudget_le_of_block_pos`
- `mobiusGammaXiCoupledErrorSourceOperator_selfAdjoint`
- `mobiusGammaXiCoupledErrorSingularOperator_selfAdjoint`
- `tendsto_mobiusGammaXiCoupledErrorSourceOperator_norm`
- `tendsto_mobiusGammaXiCoupledErrorSingularBudget_graphBudget`
- `exists_mobiusGammaXiCoupledErrorFiniteSelfAdjointBoundaryTransport`

Verification protocol:

- leaf check: `lake env lean GaloisForLFunctions/RHTower/MobiusGammaXiCoupledErrorFiniteSelfAdjointBoundaryTransport.lean`
- target build only: `lake build GaloisForLFunctions.RHTower.MobiusGammaXiCoupledErrorFiniteSelfAdjointBoundaryTransport`
- axiom audit in `/tmp`; forbidden declaration scan; formal lint
- wired into `formal/GaloisForLFunctions/RHTower.lean`; umbrella build intentionally not run

Audit result on 2026-08-18: leaf check and target build passed. Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`; forbidden declaration scan is clean. Repository-wide
lint reaches this RHTower module but exits on six unrelated pre-existing HTGeometry modules absent
from `GaloisForLFunctions.HTGeometry` umbrella.

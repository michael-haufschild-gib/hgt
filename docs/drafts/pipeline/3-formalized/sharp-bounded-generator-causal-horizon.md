# Sharp bounded-generator causal horizon

- **ID:** sharp-bounded-generator-causal-horizon
- **Stage:** 3-formalized
- **Type:** CANDIDATE
- **Date:** 2026-07-28
- **Parent article:** `local-horizon-quantum-return-law-main.tex`

## Exact question

For two bounded generators whose first \(N\) scalar response coefficients
agree, what is the strongest universal linear action scale below which their
later responses must merge?

## Frontier

- `[CORPUS]` `boundedGeneratorResponse_difference_eq_tail_of_prefix` gives
  exact cancellation of the first \(N\) scalar response terms on every
  complete complex normed space.
- `[CORPUS]`
  `boundedGeneratorResponse_difference_norm_le_of_prefix` bounds the
  remaining response by
  \[
    2\|\ell\|\|x\|e^u\frac{u^N}{N!},\qquad u=\|z\|\Lambda.
  \]
- `[CORPUS]` `persistentBoundedGeneratorSeparation_forces_linear_scale`
  consequently gives only \(u>N/(3e)\) eventually.
- `[LITERATURE]` quantum speed limits bound motion of a known state or
  distinguishability of known channels. They do not state this common-jet
  extrapolation threshold.
- `[LOCAL-RESEARCH]` the parent article has a matching local-chain upper
  construction at \(u=O(N)\), but its lower constant is inherited from the
  coarse exponential remainder.

The loss is exact: replacing the exponential tail by its first term times
\(e^u\) is too coarse when \(u\) itself grows linearly with \(N\).

## Conjecture

`[CONJECTURE]` Let \(X\) be a complete complex normed space, \(G,K:X\to X\)
bounded with \(\|G\|,\|K\|\le\Lambda\), \(x\in X\), and
\(\ell:X\to\mathbb C\) continuous. If
\[
  \ell(G^m x)=\ell(K^m x),\qquad 0\le m<N,
\]
where \(N>0\), then at the critical action \(u=\|z\|\Lambda\le N/e\),
\[
 \left|\ell(e^{zG}x)-\ell(e^{zK}x)\right|
 \le
 \frac{4\|\ell\|\|x\|}{\sqrt{2\pi N}}.
\tag{C}
\]
Consequently every fixed positive response gap along \(N\to\infty\)
eventually forces
\[
  \|z\|\Lambda>N/e.
\tag{N}
\]
For self-adjoint nearest-neighbour endpoint returns, \(N=2R+3\), so a fixed
return-probability gap eventually forces
\[
  \Lambda_R|T|>(2R+3)/e.
\tag{L}
\]

## Hostile attack before proof

1. **False at the boundary?** A Lagrange remainder produces
   \(e^{N/e}(N/e)^N/N!\), which grows exponentially. This does not refute
   the conjecture; it diagnoses the Lagrange estimate as unusable.
2. **Tail ratio failure?** For the exact exponential tail, consecutive
   terms have ratio \(u/(N+j+1)\). Under \(u\le N/e\), every ratio is
   strictly below \(1/2\), because \(e>2\). The tail is therefore at most
   twice its first term.
3. **First-term failure?** Stirling's global lower bound gives
   \(N!\ge\sqrt{2\pi N}(N/e)^N\), so the first term is at most
   \(1/\sqrt{2\pi N}\).
4. **Hidden finite-dimensional premise?** None enters: the exact scalar
   response series and coefficient norm bound already hold on arbitrary
   complete complex normed spaces.
5. **Quantum gauge failure?** The local application uses the already proved
   common energy-origin shift and centred norm certificate.
6. **Claim of optimality?** `(C)` proves the exact critical coefficient for
   this universal vanishing theorem. No sharpness witness is claimed on this
   card; “optimal” is forbidden until a matching obstruction is proved.

Verdict: `SURVIVES PRELIMINARY ATTACK`.

## Dependency-closed paper proof

Put \(u=\|z\|\Lambda\). Exact cancellation of the first \(N\) terms and the
coefficient estimate
\[
 |\ell(G^m x)-\ell(K^m x)|
 \le 2\|\ell\|\|x\|\Lambda^m
\]
give
\[
 |F_G(z)-F_K(z)|
 \le
 2\|\ell\|\|x\|
 \sum_{j=0}^{\infty}\frac{u^{N+j}}{(N+j)!}.
\tag{1}
\]

For every \(j\ge0\),
\[
 (N+j)!\ge N!(N+1)^j.
\tag{2}
\]
Indeed, the \(j\) new factors in \((N+j)!/N!\) are all at least \(N+1\).
Since \(u\le N/e\), \(N>0\), and \(e>2\),
\[
 \frac{u}{N+1}
 \le \frac{N}{e(N+1)}
 < \frac12.
\tag{3}
\]
Equations (2)--(3) imply
\[
 \sum_{j=0}^{\infty}\frac{u^{N+j}}{(N+j)!}
 \le
 \frac{u^N}{N!}\sum_{j=0}^{\infty}2^{-j}
 =
 2\frac{u^N}{N!}.
\tag{4}
\]
Stirling's global lower bound
\[
 N!\ge \sqrt{2\pi N}\left(\frac Ne\right)^N
\tag{5}
\]
and \(u\le N/e\) give
\[
 \frac{u^N}{N!}\le\frac1{\sqrt{2\pi N}}.
\tag{6}
\]
Substituting (4)--(6) into (1) proves `(C)`.

The right side of `(C)` tends to zero as \(N\to\infty\). If a fixed
positive response gap persisted while \(u\le N/e\) occurred cofinally, it
would contradict `(C)` along that cofinal subsequence. Hence `(N)` holds
eventually.

For endpoint return amplitudes of radius-\(R\) self-adjoint
nearest-neighbour paths, exact local equality fixes scalar moments through
order \(2R+2\), hence \(N=2R+3\). A common energy shift preserves return
probability and supplies the centred bound. Unit amplitudes obey
\[
 \big||a|^2-|b|^2\big|\le2|a-b|.
\]
Thus the critical probability bound is
\[
 |P_J(t)-P_K(t)|
 \le \frac{8}{\sqrt{2\pi(2R+3)}}
\quad\text{when}\quad
\Lambda|t|\le(2R+3)/e.
\tag{7}
\]
Its right side tends to zero, proving `(L)`.

All proof obligations are closed on paper.

## External collision audit

Targeted searches covered quantum speed limits, common-moment and Krylov
model reduction, exponential-response error bounds, Hamiltonian learning,
and the closest quantum-extrapolation work. Moment-matching literature
establishes interpolation and reduced-order approximation. Quantum speed
limits constrain motion or discrimination. The closest extrapolation paper,
Manos--Weilenmann--Navascués, establishes energy-constrained fog banks and
precision costs. No checked source states the critical \(N/e\)
common-response-jet law or its radius-\(R\) local-return consequence.
Search cannot establish priority.

## Status

- `[LEAN-PROVED]` exact statements `(C)`, `(N)`, `(7)`, `(L)`.
- Formal declarations:
  - `real_exp_sub_sum_le_twice_first_at_critical`
  - `factorial_first_term_le_inv_sqrt_at_critical`
  - `real_exp_sub_sum_le_inv_sqrt_critical`
  - `boundedGeneratorResponse_difference_norm_le_of_prefix_exactTail`
  - `boundedGeneratorResponse_critical_bound`
  - `persistentBoundedGeneratorSeparation_forces_critical_scale`
  - `localCausalHorizon_probability_bound_critical_gauge`
  - `persistentCofinalSeparation_forces_critical_centeredEnergyTime`
- `[NOVELTY UNVERIFIED]` independent expert priority review remains required.

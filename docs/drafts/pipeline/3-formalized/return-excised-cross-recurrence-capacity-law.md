# Return-excised cross-recurrence capacity law

- **ID:** return-excised-cross-recurrence-capacity-law
- **Stage:** 3-formalized
- **Formalized companion:** `return-excised-cross-recurrence-capacity-law-formalized.md`
- **Type:** exact observer-channel theorem / Brown-frontier reduction
- **Status:** [PAPER-PROVED] [LEAN-FORMALIZED] [APPLICATION NOVELTY UNVERIFIED]
- **Date:** 2026-08-14
- **Formal card:** ../3-formalized/return-excised-cross-recurrence-capacity-law.md

## Result

Let \(J\) be a finite sample history, \(C\) a finite observer-channel family, \(r_j\) vectors in a
real Hilbert space, \(q_c\) channel probes, \(\sigma:J\to C\) an adaptive selector, and \(w_j\ge0\).
Write

\[
 W_c=\sum_{\sigma(j)=c}w_j,\qquad L_\sigma=\sum_c W_c^2.
\]

The channel recurrence energy splits exactly as

\[
 R_\sigma=D_{\rm self}+R_{\rm cross},                              \tag{1}
\]
\[
 D_{\rm self}=\sum_j w_j^2\|r_j\|^2,\qquad
 R_{\rm cross}=
 \sum_i\sum_{\substack{j\ne i\\\sigma(i)=\sigma(j)}}
 w_iw_j\langle r_i,r_j\rangle.                                     \tag{2}
\]

Thus self-memory is charged once. Only distinct times reusing the same channel enter
\(R_{\rm cross}\).

Assume

\[
 \eta\le\langle r_j,q_{\sigma(j)}\rangle,\qquad \|q_c\|^2\le B.     \tag{3}
\]

The selector-partition law and (1) give

\[
 \eta^2L_\sigma\le B(D_{\rm self}+R_{\rm cross}).                   \tag{4}
\]

If at most \(K\) channels carry nonzero load, Cauchy on occupied loads gives the exact
return-excised capacity law

\[
 \boxed{
 \eta^2\left(\sum_jw_j\right)^2-BK D_{\rm self}
 \le BK R_{\rm cross}.}                                             \tag{5}
\]

Hence, whenever the left side is positive, bounded channel capacity forces positive genuine
cross-time recurrence. Fresh channels and diagonal self-memory cannot fake that conclusion.

Suppose additionally

\[
 \|r_j\|^2\le D,\qquad
 \langle r_i,r_j\rangle\le\mu\quad(i\ne j).                         \tag{6}
\]

Then

\[
 R_{\rm cross}\le\mu\left(L_\sigma-\sum_jw_j^2\right),              \tag{7}
\]

and therefore

\[
 \boxed{
 (\eta^2-B\mu)\left(\sum_jw_j\right)^2
 \le BK(D-\mu)\sum_jw_j^2.}                                         \tag{8}
\]

For unit weights and \(N=|J|\),

\[
 (\eta^2-B\mu)N^2\le BK(D-\mu)N.                                   \tag{9}
\]

When \(\eta^2>B\mu\), a history longer than the resulting linear capacity ceiling cannot be
captured by \(K\) channels.

## Proof

Expand every channel norm square before summing over channels. The diagonal \(i=j\) term occurs
exactly once for each sample and gives (2)'s self term; all remaining ordered pairs give
\(R_{\rm cross}\). Applying the same expansion to channel loads gives

\[
 L_\sigma=\sum_jw_j^2+
 \sum_i\sum_{\substack{j\ne i\\\sigma(i)=\sigma(j)}}w_iw_j.         \tag{10}
\]

Equation (4) is the previously proved selector-partition observer--spectral law after the exact
decomposition (1). If \(M_\sigma\le K\), then

\[
 \left(\sum_jw_j\right)^2\le M_\sigma L_\sigma\le K L_\sigma.
\]

Multiplying (4) by \(K\), substituting (1), and moving the diagonal term proves (5).

Under (6), nonnegative weights allow termwise multiplication of every cross-coherence bound,
which proves (7). Also \(D_{\rm self}\le D\sum_jw_j^2\). Substitute both bounds into (4), use
(10), and collect \(B\mu L_\sigma\) on the left. This proves the load form

\[
 (\eta^2-B\mu)L_\sigma\le B(D-\mu)\sum_jw_j^2.
\]

Multiplying the occupied-load inequality by the nonnegative gap \(\eta^2-B\mu\) and using
\(M_\sigma\le K\) proves (8). Unit weights give (9).

## Conjecture--failure--repair log

### C0 -- scalar recurrence energy can be made small

**Verdict:** false. One selected sample already pays its exact norm. Fresh self-target channels
saturate the positive observer inequality even with no off-diagonal recurrence.

### C1 -- remove diagonal memory once and preserve target labels

**Verdict:** proved in (1)--(5). Remaining source quantity is distinct-time recurrence inside
same occupied observer channel.

### C2 -- uniform pairwise coherence closes deterministic history problem

**Verdict:** proved in (6)--(9). This is a valid sufficient criterion, not a claim that an ordinary
local-Hamiltonian ensemble already supplies required \(\mu\).

### C3 -- capacity law alone proves Brown-linear growth

**Verdict:** false. If shallow-circuit channel capacity grows exponentially with circuit depth,
deterministic sample counting alone gives at best logarithmic depth in history length.
Brown-linear onset still requires quenched local-Hamiltonian anti-concentration or a stronger
growing-replica incidence estimate.

## Frontier consequence

Source obstruction is now narrower than total recurrence energy:

1. diagonal self-memory is removed from open estimate;
2. duplicate labels remain excluded by separate resolution-separation theorem;
3. only distinct-time, same-channel recurrence can support bounded-capacity adaptive shortcuts.

Remaining physical theorem must control cross recurrence for selectors produced by complete
shallow-circuit image of one ordinary time-independent local Hamiltonian, on one quenched event,
with strength sufficient for circuit capacity and approximate tubes. A direct incidence-action
proof may be stronger than uniform pairwise hypothesis (6).

## Novelty and hostile audit

Hilbert-space ingredients are classical Gram and Cauchy geometry. No standalone priority is
claimed for them. Candidate application novelty is exact diagonal removal and same-channel reuse
law inside static-Hamiltonian adaptive circuit-shortcut programme; external priority remains
unaudited.

A hostile reviewer must reject any statement that this theorem proves:

- Brown--Susskind linear growth or first onset;
- plateau time scale or first low-complexity recurrence scale;
- quenched local-Hamiltonian coherence bound;
- black-hole interior growth, holography, or gravitational dynamics.

Closed result is sharp deterministic reduction. Remaining work is hard local-Hamiltonian
probability and circuit incidence.


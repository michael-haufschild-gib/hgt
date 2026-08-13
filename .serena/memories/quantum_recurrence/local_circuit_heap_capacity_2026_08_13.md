# Local-circuit heap capacity advance (2026-08-13)

Paper-proof card: docs/drafts/pipeline/2-fully-proven/local-circuit-heap-capacity-law.md

For finite gate alphabet Sigma (M letters) with dependence graph max degree Delta, quotient circuit words only by swaps of disjoint-support gates. If h_l counts trace/heaps of length l, pair projections prove
h_l <= binom(M+l-1,l) 2^(Delta l), also h_l <= M^l.
Thus H_s=sum_{l<=s}h_l <= (s+1)binom(M+s-1,s)2^(Delta s), and
log H_s <= Delta s log 2 + M log(e(1+s/M)) + log(s+1).
For 1D fixed finite local dictionary, M=O(n), Delta=O(1), D=2^n, s=Theta(D), so log H_s <= Delta s log2+o(D)=O(D). This removes raw-word s log n overcount caused by reorderings of disjoint gates.

Heap Green reporter:
Z(z)=sum_tau z^|tau| <= (1-2^Delta z)^(-M);
G_A,z(x)=sum_tau z^|tau| 1_{ev(tau)A}(x);
nu{C_A<=s} <= z^-s int G dnu.
Under uniform target mass B, optimize z=s/[2^Delta(M+s)] to obtain
B 2^(Delta s)(1+M/s)^s(1+s/M)^M.

Combining existing Choi phase cap B_D(eps)=exp[-alpha_eps D+o(D)] with heap count gives completed-phase and all-late fixed-shell local-H plateau lower bound C_eps > cD for every c<alpha_eps/(Delta log2), with exponentially high ensemble probability. Conserved-source witness remains nonzero at all times. This is plateau only; not Brown first-cut.

Exact remaining first-cut object:
I_heap_s(nu_t,A)=sum_{l<=s} sum_{|tau|=l} nu_t(ev(tau)A),
with nu_t{C_A<=s}<=I_heap_s.
Need quenched bound after common return/fast-forwardable-carrier excision, now paying intrinsic Delta s log2 rather than s log M_n. Circuit preparation/Bellman structure remains essential due static-orbit-net no-go.

No Lean written or built because corpus refactor is active. External novelty of application remains unverified; trace monoids themselves are classical.
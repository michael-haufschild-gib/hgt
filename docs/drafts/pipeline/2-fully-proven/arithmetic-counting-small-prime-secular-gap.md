# The arithmetic secular root determines every single-prime gap

- **ID:** ACP-SMALL-PRIME-SECULAR-GAP
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean formalization follows)
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Sources:** arithmetic-counting-parity-secular-data.md; arithmetic-counting-finite-secular-criterion.md; arithmetic-counting-parity-resolvent-limit.md; arithmetic-counting-small-prime-gap-boundary.md in stage three
- **Statement:** For every prime p, the greatest uniform hyperplane gap of prime parity is min(2 log 2,alpha_p), where alpha_p is the unique root of its counted arithmetic secular series. For p<11 it is exactly alpha_p.

## Exact arithmetic data

Put c_p=(p-1)/(p+1), a_0=c_p,
`a_k=2 c_p (-1)^k/sqrt(phi(p^k))` for k>=1,
D_0=0, and `D_k=k log p+log p/(p-1)` for k>=1.
The counted coefficients have squared sum one. The already formalized
secular data give a unique root alpha_p in (0,D_1) of

`F_p(s)=sum_(k>=0) a_k^2/(D_k-s)`.

This root satisfies `0<alpha_p<p log(p)/(p+3)`. Since c_p is nonzero,
the same root is characterized by the normalized series

`-1/s + sum_(k>=1) 4/(phi(p^k)(D_k-s)) = 0`.

Write g_0=2 log 2 and delta_p=min(g_0,alpha_p). The assertion is the
exact classification

`HasHyperplaneGap(omega_p,g) iff g<=delta_p`,

where omega_p(n)=(-1)^(v_p(n)). In particular the largest allowed value
is attained in the epsilon definition of a uniform hyperplane gap.

## Closed proof

### 1. The actual finite reciprocal reading

At horizon N let e_i be an orthonormal eigenbasis of the literal full
prime matrix P_N, with eigenvalues lambda_i. Put
`E_i=log N-lambda_i-gamma`, `v=v_(p,N)`, `b_i=<v,e_i>`, and

`R_(p,N)(s)=sum_i b_i^2/(E_i-s)`.

For every 0<s<g_0, the concrete resolvent-limit theorem gives
`R_(p,N)(s)->F_p(s)` along all positive integer horizons. Its proof retains
every eigenline: each finite tower packet has the counted coordinate
limits, while the omitted reciprocal sum is bounded by its omitted mass
divided by a fixed positive spectral separation. The tower mass exhausts
one, and the actual bounded spectral count excludes an additional low line.

### 2. Exact finite form equivalence

Fix 0<s<g_0. Eventually the actual ground energy is below s, all other
energies exceed s, and the parity coefficient at the ground is nonzero.
The first statement follows from ground energy convergence to zero; the
second from the singleton spectral count at a threshold between s and
g_0; the third from convergence of its squared coefficient to c_p^2>0.

The finite Hermitian criterion says that the lower bound

`(gamma+s)||u||^2 <= log N ||u||^2-<P_N u,u>` for every u perpendicular to v

holds exactly when

`(s-E_0) sum_(i!=0) b_i^2/(E_i-s) <= b_0^2`.

Because s-E_0 is positive, this is exactly `R_(p,N)(s)<=0` after
separating the ground term. This is an equivalence for the full hyperplane.

The map y_n=omega_p(n)x_n preserves squared mass, and

`sum_(n<=N) omega_p(n)y_n/sqrt n = sqrt(H_N) <v,y>`.

The parity signs square to one. Thus orthogonality to v corresponds exactly
to the original harmonic constraint `sum x_n/sqrt n=0`, and the matrix
quadratic form is the literal atomic prime form of omega_p*x. Consequently
the Hermitian bound above is equivalent to the finite-horizon inequality
with prime gap s. Both directions use the explicit sign isometry and zero
extension; they require no approximation.

### 3. Root sign and attainment

Every positive tower energy is at least g_0. The secular function is
strictly increasing between zero and D_1. Its unique zero is alpha_p,
so F_p(s)<0 if 0<s<min(g_0,alpha_p), and F_p(s)>0 if
alpha_p<s<g_0. Summability and monotonicity are the proved secular data.

Let epsilon>0. Since delta_p>0, choose
`max(0,delta_p-epsilon)<s<delta_p`. The negative limit F_p(s) makes
R_(p,N)(s) negative eventually. By the exact finite equivalence this
proves the prime-form bound at gap s, hence the bound at gap
`delta_p-epsilon`. Its horizon may depend on epsilon, as allowed in
`HasHyperplaneGap`. Thus delta_p itself is attained.

### 4. Necessary upper bound

Let g be any hyperplane gap of omega_p. The already proved all-sign
ceiling gives g<=g_0. If alpha_p<g, choose alpha_p<s<g. Then 0<s<g_0
and F_p(s)>0. Use the assumed gap with epsilon=(g-s)/2: its eventual
form inequality implies the finite bound at gap s. The exact equivalence
therefore forces R_(p,N)(s)<=0 eventually. But its strictly positive limit
forces R_(p,N)(s)>0 eventually, a contradiction. Hence g<=alpha_p,
and therefore g<=delta_p.

Attainment and this upper bound prove greatestness. Every g<=delta_p is
a gap by downward closure: decreasing the gap only increases the allowed
coefficient of the nonnegative squared mass. This proves the complete iff.

### 5. Exact small-prime values and sharp comparison

The established cutoff says that omega_p attains g_0 exactly when p>=11.
If p<11 and alpha_p>=g_0, the newly proved attained value delta_p would
equal g_0, a contradiction. Thus alpha_p<g_0 and the greatest gap is
alpha_p. If p>=11, the existing attained gap g_0 and the necessary secular
upper bound force alpha_p>=g_0. Therefore

`alpha_p<2 log 2 iff p<11`.

Finally every gap g satisfies
`g<=alpha_p<p log(p)/(p+3)`, making the earlier two-mode bound strict
for every prime. No separate large-prime endpoint or repeated small-prime
logarithmic estimate is used.

## Scope and audit

The contribution is the exact constrained gap of the actual finite prime
matrices, not a new abstract secular equation. Its inputs are the counted
parity tower and its uniform exhaustion, actual bounded-spectrum counting,
finite reciprocal criterion, and the concrete resolvent convergence.
No asymptotic spectral premise is added to the final theorem. No limiting
operator or uncontrolled exchange of horizon and conductor limits is used.

The p>=41 endpoint remains discarded. The p>=11 endpoint comes from the
existing independent valuation-box proof; this work uses that endpoint to
locate the secular root relative to the universal ceiling. The exact values
for p=2,3,5,7 are supplied by a unique explicit series root, without numerical
experiments. Complete Weil positivity and the wider producer programme
remain separate open obligations.

## Formalization

The eight-endpoint draft is `/tmp/acp-exact-parity-gap-check.lean`.
It imports the concrete resolvent leaf and the existing small-prime cutoff.
The new resolvent olean and the small-prime boundary olean are required
before its check; existing oleans are not rebuilt.

- [x] Closed dependency-complete paper proof.
- [ ] All eight Lean endpoints and transitive axiom audit.
- [ ] Canonical source audit, umbrella, README, durable evidence and cleanup.

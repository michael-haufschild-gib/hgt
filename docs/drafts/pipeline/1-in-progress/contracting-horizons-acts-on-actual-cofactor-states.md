# Contracting horizons acts on actual cofactor states

- **ID:** contracting-horizons-acts-on-actual-cofactor-states
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / ACTUAL-STATE TRANSPORT
- **Parent:** [Q-III](q-iii-escape-state-classification.md)

## Target

For every actual common limit L and positive integer p with K(p,p)>0,
construct an actual common limit L_p with

    K_p(j,k) = K(p*j,p*k) / K(p,p).

On escape this comes from integer-contracted observation horizons. On
admission the common kernel is unique; complete infinite pronic pairing
scales by 1/p, yielding the same normalized kernel. No choice of an abstract
positive kernel may replace the required actual subsequence.

## Paper mechanism to audit

At T, set N=floor(T/p), U=p*(N+1)-1. Complete blocks give
Q_U(D_p u,D_p v)=Q_N(u,v)/p. The omitted interval (T,U] lies in one quotient
fibre. If u(0)=v(0)=0 and |u(n)|,|v(n)|<=n, its absolute pairing is at most
1/p, by the existing full-fibre pronic mass. Thus

    |Q_T(D_p u,D_p v)-Q_N(u,v)/p| <= 1/p.

Every actual cofactor u_j(n)=A(floor(n/j)) satisfies this linear bound.
After dividing by E(T) on escape, the error vanishes. The already derived
ratio E(N)/E(T) tends to p*K(p,p). Hence, if K(p,p)>0, the normalized mixed
Gram at horizon N converges to K(p*j,p*k)/K(p,p). Since N tends to infinity,
extract a strictly increasing subsequence of N-1 to package an actual state.
The finitely many N=0 terms are irrelevant but must be handled explicitly.

## Positive zero branch

If K(p,p)=0, numeric horizon order forces all v_q with q>=p to vanish;
in particular D_p vanishes on every cyclic generator and hence on the
complete module. The actual module is finite-dimensional of dimension at
most p-1. Thus the missing normalization at zero has an exact finite
algebraic interpretation, not an arbitrary choice of state.

## Scope

This transports actual state space under horizon contractions. It does not
claim that a given state is fixed, that its energy ratios are multiplicative,
or that its hull lies on a Kronecker curve. A subsequent composition law
must account for zero intermediate diagonal values.

## Gates

- [x] Corpus search for exact mixed truncated-fibre laws initiated.
- [ ] Audit and formalize the uniform mixed last-fibre error.
- [ ] Actual cofinal subsequence construction with horizon shift by one.
- [ ] Admitted branch from full pairing convergence.
- [ ] Exact zero-dilation branch.
- [ ] Composition, hull and module consequences.

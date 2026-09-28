# Prime-deletion causal modes and the Gaussian boundary trace

- **ID:** SQB-SIEVE-MODE
- **Stage:** 3-formalized (paper theorem; Lean formalization complete)
- **Type:** THEOREM (paper)
- **Routes:** SQB, WS2, L
- **Statement:** At every interior Xi zero, each finite prime-deleted theta source has a two-ended causal mode, but cofinal deletion sends these modes locally to a Gaussian-seed response with an explicit nonzero negative-cusp radiation coefficient.

## Goal

The [prime-deletion source theorem](theta-prime-deletion-spectral-escape.md)
shows that the exact Xi divisor survives every finite deletion while the
sources converge locally to a zero-free Gaussian seed. The theorem below
identifies the missing datum at the level of the *causal mode*, which is the
common function used by the SQB and Hedenmalm carriers. It does not orient
that datum or prove RH.

## Exact mode graph [PROVED HERE]

Use the notation of the prime-deletion source theorem:

```text
k(x) = sum_(n>=1) a_n(x),
a_n(x) = n^(-1/2) h(x+log n),
k_S = product_(p in S) (1-p^(-1/2) T_(log p)) k
    = sum_((n, product S)=1) a_n.
```

Let `S_j` be any increasing cofinal sequence of finite prime sets. Fix
`omega` with `|Re omega|<1/2` and `Xi_C(i*omega)=0`. For a source `f`
whose right-tail integral converges, define its right-anchored causal
response by

```text
U_f,omega(x) = exp(-omega*x) * integral_x^infinity exp(omega*t)*f(t) dt.
```

It satisfies `(partial_x+omega) U_f,omega=-f`. Every finite `k_S` is a
finite sum of translates of the two-ended rapidly decreasing theta
source. The exact transform formula gives

```text
integral_R exp(omega*t)*k_S(t) dt
  = Xi_C(i*omega) * product_(p in S)(1-p^(-1/2-omega)) = 0.
```

Consequently the same response has the left-anchored formula

```text
U_kS,omega(x)
  = -exp(-omega*x) * integral_-infinity^x exp(omega*t)*k_S(t) dt. (1)
```

Both formulas and the two-ended rapid decay make `U_kS,omega` a
two-ended rapidly decreasing `L²(R)` solution. This is a statement about
the causal differential equation; it does not assert that every such
solution is an eigenvector of an unchanged SQB operator.

For each finite `x_0`, the atom expansion has a common integrable
majorant on `[x_0,infinity)` after multiplication by
`exp(Re(omega)*t)`: the explicit Gaussian atom decays rapidly in
`n*exp(t)`, and the sum over `n` converges absolutely there. Dominated
convergence therefore gives, locally uniformly in `x`,

```text
U_kSj,omega(x) --> U_h,omega(x).                                  (2)
```

The seed transform is explicit on this strip:

```text
H(omega) := integral_R exp(omega*t)*h(t) dt
          = (omega-1/2)*Gamma(omega/2+5/4)*pi^(-omega/2-1/4).
```

It is nonzero: `omega` is strictly inside the strip, and Gamma has no
zeros. The right-anchored seed response has the exact boundary trace

```text
lim_(x-->-infinity) exp(omega*x)*U_h,omega(x) = H(omega) != 0.     (3)
```

For every finite `S_j`, the corresponding limit is zero by (1).
Equations (2)--(3) prove the noncommutation of cofinal deletion and the
negative-cusp boundary trace:

```text
lim_j lim_(x-->-infinity) exp(omega*x)*U_kSj,omega(x) = 0,
lim_(x-->-infinity) lim_j exp(omega*x)*U_kSj,omega(x) = H(omega).  (4)
```

When `Re omega>=0`, (3) also gives
`|U_h,omega(x)| ~ |H(omega)|*exp(-Re(omega)*x)` at the negative cusp.
Its `L²(-infinity,0)` norm is infinite. Local convergence (2), applied
on every finite interval and then exhausted toward `-infinity`, yields

```text
lim_j ||U_kSj,omega||_(L²(R)) = infinity  if Re omega>=0.        (5)
```

In particular, a right-of-centre zero would create exponential escape
at rate `Re omega`; a critical zero creates nondecaying oscillatory
escape. The divergence in (5) therefore does **not** distinguish RH.
The exact coefficient and rate in (3) are the positive content: they
identify the boundary mode which a source-faithful spectral transfer
must retain. Any SQB/WS2 self-adjoint realization built by cofinal
prime deletion must control a boundary trace or a renormalized
two-port current, rather than rely on compact-local mode convergence.

## Whole-chain status

This is a paper proof of a mode-level singular boundary law, not a
source sign law. It does not prove the cross-prime cancellation required
by the [causal Möbius--theta criterion](causal-mobius-theta-boundary-criterion.md),
nor the SQB leakage-plus-drift orientation. The next decisive theorem
would have to bound or orient the *reflected difference* of the two
boundary growth channels after retaining the nonzero trace (3).
Equations (1)--(5) are formalized in Lean in
`GaloisForLFunctions.RHTower.ThetaPrimeDeletionCausalMode`; see
`sqb-prime-deletion-causal-mode-escape-formalized.md`. No computation was used.

The [finite-prime moving-cusp criterion](finite-prime-moving-cusp-causal-criterion.md)
identifies an RH-equivalent directed atom port of this same deletion
family at `x=-log N`, with prime horizon `N log N`. Its Gaussian
truncation error is superpolynomial; signed cancellation inside the
finite port remains the source-side obstacle.

## Log

- 2026-09-28: formalized in Lean (`ThetaPrimeDeletionCausalMode`, wired, olean built, axioms
  standard); moved to stage 3. Certificate: `sqb-prime-deletion-causal-mode-escape-formalized.md`.
